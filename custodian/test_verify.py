from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import verify
from review import review as reviewer


SOURCE = Path(__file__).resolve().parents[1]
VERIFIER = Path(verify.__file__).resolve()


class ConstructionVerifierTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.base = self.root / "base"
        self.base.mkdir()
        self.git(self.base, "init", "-q", "-b", "main")
        self.write(self.base, ".gitignore", ".lake/\n")
        self.write(self.base, "CasCatalogue/Sealed.lean", "def original : Nat := 0\n")
        self.write(self.base, verify.LEDGER, json.dumps({
            "assertions": {"original": "a" * 64}, "corrections": [],
        }))
        self.boundary = {
            "boundary": ["CasCatalogue/*", "CasAcceptance/*", "custodian/boundary.json"],
            "append_only": [],
        }
        self.write(self.base, "custodian/boundary.json", json.dumps(self.boundary))
        packages = []
        for name in verify.CHAIN:
            package = self.base / verify.PACKAGES / name
            package.mkdir(parents=True)
            self.git(package, "init", "-q", "-b", "main")
            self.write(package, "README.md", name + "\n")
            self.git(package, "add", "README.md")
            self.git(package, "commit", "-qm", "original package")
            packages.append({"name": name, "rev": self.git(package, "rev-parse", "HEAD")})
        self.write(self.base, "lake-manifest.json", json.dumps({"packages": packages}))
        self.git(self.base, "add", ".")
        self.git(self.base, "commit", "-qm", "original source")
        self.key = self.root / "owner"
        subprocess.run(
            ["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", str(self.key)],
            check=True, capture_output=True,
        )
        self.fingerprint = verify.key_fpr(self.key.with_suffix(".pub").read_text())
        self.seal = self.root / "seal.json"
        seal = verify.build_seal(
            self.base, self.boundary["boundary"], [], verify.sha(VERIFIER.read_bytes()), "fixture",
        )
        seal["reviewer_keys"] = {}
        seal["escalation_keys"] = {}
        self.seal.write_text(json.dumps(seal))
        subprocess.run(
            ["ssh-keygen", "-q", "-Y", "sign", "-f", str(self.key),
             "-n", verify.NAMESPACE, str(self.seal)],
            check=True, capture_output=True,
        )
        baseline = self.run_verifier(self.base, construction=False)
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)

    def git(self, repo: Path, *args: str) -> str:
        return subprocess.run(
            ["git", "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false",
             "-c", "user.name=fixture", "-c", "user.email=fixture@example.test",
             "-C", str(repo), *args],
            check=True, capture_output=True, text=True,
        ).stdout.strip()

    def write(self, repo: Path, relative: str, text: str) -> None:
        path = repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def case(self, name: str) -> Path:
        repo = self.root / name
        shutil.copytree(self.base, repo)
        boundary = json.loads((SOURCE / "custodian/boundary.json").read_text())
        self.write(repo, "custodian/boundary.json", json.dumps(boundary))
        return repo

    def run_verifier(self, repo: Path, *, construction: bool) -> subprocess.CompletedProcess[str]:
        command = [
            sys.executable, "-B", str(VERIFIER), "--repo", str(repo), "--seal", str(self.seal),
            "--key", str(self.key.with_suffix(".pub")), "--trusted-fpr", self.fingerprint,
        ]
        if construction:
            command.append("--construction")
        return subprocess.run(command, capture_output=True, text=True)

    def test_actual_kernel_control_sources_are_construction_owners(self) -> None:
        repo = self.case("actual-controls")
        for relative, source in (
            ("CasCompiler/Lower.lean", "initialize registerTraceClass `cas.lower\n"),
            ("CasCompiler/Read.lean", 'syntax (name := sourceExpression) "cas_source% " cas_term : term\n'),
            ("CasRuntime/Environment.lean", "initialize registerTraceClass `cas.environment\n"),
        ):
            self.write(repo, relative, source)
            self.git(repo, "add", relative)
        result = self.run_verifier(repo, construction=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_actual_admission_name_observations_are_not_proof_escapes(self) -> None:
        repo = self.case("actual-names")
        for relative, source in (
            ("CasCompiler/SourceInstanceTests.lean",
             "          admission.entry.admission == some ``CasCatalogue.Foundation.FiniteSubsets.admit &&\n"),
            ("CasCompiler/SourceRingTests.lean",
             "          admission.entry.admission == some ``CasCatalogue.Algebra.Units.admit &&\n"),
            ("CasCompiler/SourceViewTests.lean",
             "        ((← SourceTest.visitNativeData (fun expression => pure "
             "(expression.isConstOf ``CasCatalogue.Algebra.Series.admit)) value) > 0) &&\n"),
        ):
            self.write(repo, relative, source)
            self.git(repo, "add", relative)
        result = self.run_verifier(repo, construction=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_quoted_and_qualified_names_are_not_tactics(self) -> None:
        repo = self.case("names")
        self.write(repo, "CasCompiler/Names.lean",
                   "def quoted := ``Example.admit\n"
                   "def unqualifiedQuoted := ``admit\n"
                   "def simpleQuoted := `admit\n"
                   "def qualified := Example.admit\n"
                   "def admit (value : Nat) : Nat := value\n")
        self.git(repo, "add", "CasCompiler/Names.lean")
        result = self.run_verifier(repo, construction=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_proof_escapes_remain_hard_in_construction(self) -> None:
        cases = (
            ("plain", "admit", "example : True := by admit\n"),
            ("next-command", "admit", "example : True := by\n  admit\ndef later := 1\n"),
            ("comment-next-command", "admit",
             "example : True := by\n  admit /- hidden -/\ndef later := 1\n"),
            ("parenthesized", "admit", "example : True := by\n  (admit)\n"),
            ("nested", "admit", "example : True := by\n  first\n  | admit\n  | exact True.intro\n"),
            ("nested-term", "admit", "example : True := by exact (by admit)\n"),
            ("macro", "admit", 'macro "escape" : tactic => `(tactic| admit)\n'),
            ("sorry", "sorry", "example : True := by sorry\n"),
            ("axiom", "axiom", "axiom invented : False\n"),
            ("native", "native_decide", "example : True := by native_decide\n"),
            ("reduction", "ofReduceBool", "def invented := Lean.ofReduceBool\n"),
            ("skip-check", "debug.skipKernelTC", "set_option debug.skipKernelTC true\n"),
        )
        for name, rule, source in cases:
            with self.subTest(name=name):
                repo = self.case(name)
                self.write(repo, "CasCompiler/Escape.lean", source)
                self.git(repo, "add", "CasCompiler/Escape.lean")
                result = self.run_verifier(repo, construction=True)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("banned construct: CasCompiler/Escape.lean:" + rule + ":", result.stdout)

    def test_construction_control_owners_gain_no_semantic_or_leaf_authority(self) -> None:
        cases = (
            ("registry", "CasCompiler/Injected.lean", "def injected := normalized_registry\n",
             "outside the boundary: CasCompiler/Injected.lean:semantic-registration:"),
            ("semantic-entry", "CasRuntime/Injected.lean", "def injected := addSemanticEntryChecked\n",
             "outside the boundary: CasRuntime/Injected.lean:semantic-registration:"),
            ("persist-semantic", "CasCompiler/Injected.lean", "def injected := persistSemanticEntry\n",
             "outside the boundary: CasCompiler/Injected.lean:semantic-registration:"),
            ("semantic-module", "LeanCategories/Injected.lean", "def injected := 0\n",
             "outside the boundary: LeanCategories/Injected.lean:semantic-module-downstream"),
            ("leaf-source", "CasLeaves/Injected.lean", "def injected := 0\n",
             "leaf file in lean-cas-dsl: CasLeaves/Injected.lean"),
            ("leaf-registration", "CasCompiler/Injected.lean", "register_leaf {}\n",
             "leaf registration in lean-cas-dsl: CasCompiler/Injected.lean"),
            ("unowned-control", "Other/Injected.lean", 'syntax "injected" : command\n',
             "outside the boundary: Other/Injected.lean:syntax:"),
        )
        for name, relative, source, expected in cases:
            with self.subTest(name=name):
                repo = self.case(name)
                self.write(repo, relative, source)
                self.git(repo, "add", relative)
                result = self.run_verifier(repo, construction=True)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(expected, result.stdout)

    def test_reviewer_construction_keeps_original_semantic_authority(self) -> None:
        trusted = self.case("trusted")
        self.git(trusted, "add", "custodian/boundary.json")
        self.git(trusted, "commit", "-qm", "current construction owners")
        specification = json.loads((trusted / "custodian/boundary.json").read_text())
        seal = verify.build_seal(
            trusted, specification["boundary"], specification["append_only"],
            verify.sha(VERIFIER.read_bytes()), "construction comparison",
        )
        for owner in ("CasCompiler", "CasRuntime"):
            with self.subTest(owner=owner):
                candidate = self.root / owner
                shutil.copytree(trusted, candidate)
                relative = owner + "/Injected.lean"
                self.write(candidate, relative, "def injected := addSemanticEntryChecked\n")
                self.git(candidate, "add", relative)
                hard, _ = reviewer.classify(verify.check(candidate, seal), construction=True)
                expected = "outside the boundary: " + relative + ":semantic-registration:"
                self.assertTrue(any(finding.startswith(expected) for finding in hard), hard)

    def test_original_assertions_and_ledger_fields_stay_protected(self) -> None:
        for name in ("changed", "removed", "corrections"):
            with self.subTest(name=name):
                repo = self.case(name)
                ledger = json.loads((repo / verify.LEDGER).read_text())
                if name == "changed":
                    ledger["assertions"]["original"] = "b" * 64
                elif name == "removed":
                    del ledger["assertions"]["original"]
                else:
                    ledger["corrections"].append({"reason": "rewritten"})
                (repo / verify.LEDGER).write_text(json.dumps(ledger))
                result = self.run_verifier(repo, construction=True)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                expected = ("sealed ledger field changed:" if name == "corrections"
                            else "sealed assertion changed or removed in the ledger: original")
                self.assertIn(expected, result.stdout)

    def test_package_identity_cleanliness_and_links_stay_protected(self) -> None:
        for name in ("dirty", "revision", "missing", "link"):
            with self.subTest(name=name):
                repo = self.case(name)
                package = repo / verify.PACKAGES / "cas_leaf_contracts"
                if name in ("dirty", "revision"):
                    (package / "README.md").write_text("changed\n")
                    if name == "revision":
                        self.git(package, "commit", "-qam", "different revision")
                    expected = ".lake/packages/cas_leaf_contracts is not the manifest revision "
                else:
                    moved = self.root / ("moved-" + name)
                    package.rename(moved)
                    if name == "link":
                        package.symlink_to(moved, target_is_directory=True)
                        expected = ".lake/packages/cas_leaf_contracts is a link to a working tree"
                    else:
                        expected = ".lake/packages/cas_leaf_contracts is not checked out"
                result = self.run_verifier(repo, construction=True)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(expected, result.stdout)

    def test_leaf_controls_remain_prohibited_at_the_recorded_revision(self) -> None:
        repo = self.case("leaf-control")
        package = repo / verify.PACKAGES / "cas_leaves"
        self.write(package, "CasLeaves/Injected.lean", 'syntax "injected" : command\n')
        self.git(package, "add", "CasLeaves/Injected.lean")
        self.git(package, "commit", "-qm", "leaf defines syntax")
        manifest = json.loads((repo / "lake-manifest.json").read_text())
        for entry in manifest["packages"]:
            if entry["name"] == "cas_leaves":
                entry["rev"] = self.git(package, "rev-parse", "HEAD")
        (repo / "lake-manifest.json").write_text(json.dumps(manifest))
        result = self.run_verifier(repo, construction=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("leaf violation: CasLeaves/Injected.lean:syntax:", result.stdout)
        self.assertNotIn("is not the manifest revision", result.stdout)

    def test_steady_mode_keeps_the_signed_boundary(self) -> None:
        repo = self.case("steady-control")
        self.write(repo, "CasCompiler/Injected.lean", 'syntax "injected" : command\n')
        self.git(repo, "add", "CasCompiler/Injected.lean")
        result = self.run_verifier(repo, construction=False)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("sealed file changed: custodian/boundary.json", result.stdout)
        self.assertIn("outside the boundary: CasCompiler/Injected.lean:syntax:", result.stdout)

    def test_steady_mode_rejects_changed_sealed_source(self) -> None:
        repo = self.root / "steady-source"
        shutil.copytree(self.base, repo)
        (repo / "CasCatalogue/Sealed.lean").write_text("def original : Nat := 1\n")
        result = self.run_verifier(repo, construction=False)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("sealed file changed: CasCatalogue/Sealed.lean", result.stdout)

    def test_steady_mode_rejects_untrusted_or_invalid_signatures(self) -> None:
        original = self.fingerprint
        self.fingerprint = "SHA256:not-the-owner"
        untrusted = self.run_verifier(self.base, construction=False)
        self.assertEqual(untrusted.returncode, 1, untrusted.stdout + untrusted.stderr)
        self.assertIn("UNTRUSTED:", untrusted.stderr)
        self.fingerprint = original
        self.seal.write_text(self.seal.read_text() + "\n")
        invalid = self.run_verifier(self.base, construction=False)
        self.assertEqual(invalid.returncode, 1, invalid.stdout + invalid.stderr)
        self.assertIn("INVALID SIGNATURE", invalid.stderr)

    def test_steady_mode_rejects_a_broken_verdict_chain(self) -> None:
        self.write(self.base, "custodian/verdicts/000002.json", "{}\n")
        result = self.run_verifier(self.base, construction=False)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("BROKEN CHAIN: expected 000001.json", result.stderr)


if __name__ == "__main__":
    unittest.main()

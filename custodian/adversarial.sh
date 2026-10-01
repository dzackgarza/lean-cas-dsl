set -u
# usage: adversarial.sh <empty scratch dir> <trusted fpr> <lean-cas-dsl checkout>
# Each case applies one intervention to a fresh copy of the committed checkout, with the chain in
# .lake/packages at the manifest revisions, and states the verdict the seal must give.
S=$1; FPR=$2; SRC=$3
git clone -q "$SRC" "$S/src" && python3 "$S/src/scripts/ci_chain.py" "$S/src" || exit 2
n=0
# Commit in a package checkout, and record its new head in the manifest, as `lake update` does
# after an upstream commit.
pkgcommit() { # package
  git -C .lake/packages/$1 add -A
  git -C .lake/packages/$1 -c user.name=x -c user.email=x@x -c core.hooksPath=/dev/null commit -qm x
  h=$(git -C .lake/packages/$1 rev-parse HEAD)
  jq --indent 1 --arg p "$1" --arg h "$h" '(.packages[] | select(.name == $p) | .rev) = $h' \
    lake-manifest.json > "$S/manifest.$n" && cp "$S/manifest.$n" lake-manifest.json
}
LC=.lake/packages/lean_categories
run() { # name expect(0/1) setup...
  name=$1; expect=$2; shift 2
  n=$((n + 1)); t="$S/case-$n"
  cp -r "$S/src" "$t"
  (cd "$t" && eval "$@") >/dev/null 2>&1
  out=$(cd "$t" && python3 custodian/verify.py --trusted-fpr $FPR 2>&1); rc=$?
  [ $rc -ne 0 ] && rc=1
  if [ "$rc" = "$expect" ]; then r=OK; else r=FAIL; fi
  echo "$r [$name] rc=$rc :: $(echo "$out" | grep -v '^note' | sed -n 2p | head -c 150)$(echo "$out" | grep -E 'UNTRUSTED|INVALID|not a sealed' | head -c 120)"
}
L=.lake/packages/cas_leaves
run baseline 0 true
run gate-edit 1 "echo '# relax' >> scripts/check_no_leaves.py"
run kernel-edit 1 "echo '-- x' >> CasCatalogue/Semantic.lean"
run assertion-edit 1 "f=\$(ls tests/acceptance/*.cas|head -1); sed -i '0,/test /s/test /test  /' \$f; echo >> \$f"
run ledger-rewrite 1 "python3 -c \"import json;p='CasAcceptance/Permanent/admitted.json';d=json.load(open(p));k=sorted(d['assertions'])[0];d['assertions'][k]='0'*64;open(p,'w').write(json.dumps(d))\""
run ledger-correction 1 "python3 -c \"import json;p='CasAcceptance/Permanent/admitted.json';d=json.load(open(p));d['corrections'].append({'reason':'x'});open(p,'w').write(json.dumps(d))\""
run ledger-append 0 "python3 -c \"import json;p='CasAcceptance/Permanent/admitted.json';d=json.load(open(p));d['assertions']['new-one']='1'*64;open(p,'w').write(json.dumps(d))\""
run upstream-moves 0 "echo x >> .lake/packages/lean_categories/README.md; pkgcommit lean_categories"
run upstream-rule-edit 1 "echo '-- x' >> .lake/packages/lean_categories/LeanCategories/Catalogue.lean; pkgcommit lean_categories"
run upstream-rule-added 1 "echo '-- x' > .lake/packages/lean_categories/LeanCategories/Catalogue/X.lean; pkgcommit lean_categories"
run contract-edit 1 "echo '-- x' >> .lake/packages/cas_leaf_contracts/CasContract/Leaf.lean; pkgcommit cas_leaf_contracts"
run contract-moves 0 "echo x >> .lake/packages/cas_leaf_contracts/README.md; pkgcommit cas_leaf_contracts"
run leaves-move 0 "echo x >> $L/README.md; pkgcommit cas_leaves"
run upstream-rule-uncommitted 1 "echo '-- x' >> $LC/LeanCategories/Catalogue.lean"
run upstream-missing 1 "mv $LC $S/moved-lc2-\$\$"
run lakefile-edit 1 "sed -i 's/@ \"main\"/@ \"dev\"/' lakefile.lean"
run new-acceptance-test 0 "echo 'test zz-new \"src\": 1 = 1' > tests/acceptance/zz.cas; git add tests/acceptance/zz.cas"
run leaf-in-dsl 1 "mkdir -p CasLeaves; echo x > CasLeaves/X.lean; git add CasLeaves"
run register-leaf-in-tests 1 "echo 'register_leaf { }' >> CasDslTests/Cells.lean"
run semantic-module-downstream 1 "mkdir -p LeanCategories; echo x > LeanCategories/X.lean; git add LeanCategories"
run macro-outside 1 "printf 'macro_rules\n  | _ => pure default\n' > CasDslTests/Evil.lean; git add CasDslTests/Evil.lean"
run sorry-outside 1 "printf 'theorem t : False := sorry\n' > CasDslTests/S.lean; git add CasDslTests/S.lean"
run sorry-in-comment 0 "printf -- '-- sorry\n/- sorry -/\ndef s := \"sorry\"\n' > CasDslTests/C.lean; git add CasDslTests/C.lean"
run seal-tamper 1 "sed -i 's/\"format\": 1/\"format\": 2/' custodian/seal.json"
run forged-seal 1 "ssh-keygen -q -t ed25519 -N '' -f $S/forged-\$\$; cp $S/forged-\$\$.pub custodian/root.pub; python3 custodian/verify.py --make-seal; ssh-keygen -q -Y sign -f $S/forged-\$\$ -n lean-cas-custodian custodian/seal.json"
run leaf-macro 1 "printf 'macro_rules | _ => pure default\n' >> $L/CasLeaves/Foundation/Lists.lean; pkgcommit cas_leaves"
run leaf-imports-tests 1 "sed -i '1i import CasAcceptance.Standard' $L/CasLeaves/Foundation/Lists.lean; pkgcommit cas_leaves"
run leaf-semantic-module 1 "mkdir -p $L/LeanCategories; echo x > $L/LeanCategories/X.lean; pkgcommit cas_leaves"
run leaf-not-manifest-rev 1 "echo >> $L/README.md; git -C $L -c user.name=x -c user.email=x@x -c core.hooksPath=/dev/null commit -qam x"
run leaves-missing 1 "mv $L $S/moved-leaves-\$\$"
run dev-link 1 "mv .lake/packages/lean_categories $S/moved-lc-\$\$; ln -s $S/moved-lc-\$\$ .lake/packages/lean_categories"
run intent-edit 1 "echo x >> custodian/owner-intent.md"
run adversarial-edit 1 "echo '# x' >> custodian/adversarial.sh"
run boundary-shrink 1 "python3 -c \"import json;p='custodian/boundary.json';d=json.load(open(p));d['boundary'].remove('CasGates/*');open(p,'w').write(json.dumps(d))\""

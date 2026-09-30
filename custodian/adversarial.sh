set -u
# usage: adversarial.sh <scratch dir> <trusted fpr> <lean-cas-dsl checkout> <lean-cas-dsl-leaves clone>
# Each case applies one intervention to a copy and states the verdict the seal must give.
S=$1; FPR=$2; SRC=$3; LSRC=$4
run() { # name expect(0/1) setup...
  name=$1; expect=$2; shift 2
  rm -rf $S/t $S/l; cp -r $SRC $S/t; git clone -q $LSRC $S/l 2>/dev/null; git -C $S/l -c advice.detachedHead=false checkout -q c4cff1645158aa138c5f828b47de43e8b051a44e
  (cd $S/t && eval "$@") >/dev/null 2>&1
  out=$(cd $S/t && python3 custodian/verify.py --trusted-fpr $FPR --leaves $S/l 2>&1); rc=$?
  [ $rc -ne 0 ] && rc=1
  if [ "$rc" = "$expect" ]; then r=OK; else r=FAIL; fi
  echo "$r [$name] rc=$rc :: $(echo "$out" | grep -v '^note' | sed -n 2p | head -c 150)$(echo "$out" | grep -E 'UNTRUSTED|INVALID|not the sealed' | head -c 120)"
}
run baseline 0 true
run gate-exemption 1 "sed -i 's/not a reading fallback/fallback ok/' scripts/check_kernel_totality.py"
run ci-edit 1 "echo '# x' >> .github/workflows/gates.yml"
run kernel-edit 1 "echo '-- x' >> CasCatalogue/Semantic.lean"
run assertion-edit 1 "f=\$(ls tests/acceptance/*.cas|head -1); sed -i '0,/test /s/test /test  /' \$f; echo >> \$f"
run ledger-rewrite 1 "python3 -c \"import json;p='CasAcceptance/Permanent/admitted.json';d=json.load(open(p));k=sorted(d['assertions'])[0];d['assertions'][k]='0'*64;open(p,'w').write(json.dumps(d))\""
run ledger-correction 1 "python3 -c \"import json;p='CasAcceptance/Permanent/admitted.json';d=json.load(open(p));d['corrections'].append({'reason':'x'});open(p,'w').write(json.dumps(d))\""
run ledger-append 0 "python3 -c \"import json;p='CasAcceptance/Permanent/admitted.json';d=json.load(open(p));d['assertions']['new-one']='1'*64;open(p,'w').write(json.dumps(d))\""
run repin-lean-categories 1 "sed -i 's/c06aeedc8ebc16c787481a5c15a86526341a4b4e/6b2750c9de7d0a4a28fc3cc278021fe8400e2437/g' lake-manifest.json"
run repin-contract-lakefile 1 "sed -i 's/6588a86ca5d0ade8ffdabf5f7f95640d426d18f4/9fd3c17612ddf1bdb75ff510cc0f5ffb1d5a9e88/' lakefile.lean"
run repin-leaves 0 "sed -i 's/c4cff1645158aa138c5f828b47de43e8b051a44e/6c553afd27a92b26e334c6ce4e2045960b58ae02/g' lakefile.lean lake-manifest.json; git -C $S/l checkout -q 6c553afd27a92b26e334c6ce4e2045960b58ae02"
run new-acceptance-test 0 "echo 'test zz-new \"src\": 1 = 1' > tests/acceptance/zz.cas; git add tests/acceptance/zz.cas"
run leaf-in-dsl 1 "mkdir -p CasLeaves; echo x > CasLeaves/X.lean; git add CasLeaves"
run register-leaf-in-tests 1 "echo 'register_leaf { }' >> CasDslTests/Cells.lean"
run semantic-module-downstream 1 "mkdir -p LeanCategories; echo x > LeanCategories/X.lean; git add LeanCategories"
run macro-outside 1 "printf 'macro_rules\n  | _ => pure default\n' > CasDslTests/Evil.lean; git add CasDslTests/Evil.lean"
run sorry-outside 1 "printf 'theorem t : False := sorry\n' > CasDslTests/S.lean; git add CasDslTests/S.lean"
run sorry-in-comment 0 "printf -- '-- sorry\n/- sorry -/\ndef s := \"sorry\"\n' > CasDslTests/C.lean; git add CasDslTests/C.lean"
run seal-tamper 1 "sed -i 's/\"format\": 1/\"format\": 2/' custodian/seal.json"
run forged-seal 1 "rm -f $S/forged $S/forged.pub custodian/seal.json.sig; ssh-keygen -q -t ed25519 -N '' -f $S/forged; cp $S/forged.pub custodian/root.pub; python3 custodian/verify.py --make-seal; ssh-keygen -q -Y sign -f $S/forged -n lean-cas-custodian custodian/seal.json"
run leaf-macro 1 "printf 'macro_rules | _ => pure default\n' >> $S/l/CasLeaves/Foundation/Lists.lean; git -C $S/l -c user.name=x -c user.email=x@x commit -qam x; h=\$(git -C $S/l rev-parse HEAD); sed -i \"s/c4cff1645158aa138c5f828b47de43e8b051a44e/\$h/g\" lakefile.lean lake-manifest.json"
run leaf-imports-tests 1 "sed -i '1i import CasAcceptance.Standard' $S/l/CasLeaves/Foundation/Lists.lean; git -C $S/l -c user.name=x -c user.email=x@x commit -qam x; h=\$(git -C $S/l rev-parse HEAD); sed -i \"s/c4cff1645158aa138c5f828b47de43e8b051a44e/\$h/g\" lakefile.lean lake-manifest.json"
run leaf-semantic-module 1 "mkdir -p $S/l/LeanCategories; echo x > $S/l/LeanCategories/X.lean; git -C $S/l add -A; git -C $S/l -c user.name=x -c user.email=x@x commit -qm x; h=\$(git -C $S/l rev-parse HEAD); sed -i \"s/c4cff1645158aa138c5f828b47de43e8b051a44e/\$h/g\" lakefile.lean lake-manifest.json"
run leaf-unpinned 1 "echo >> $S/l/README.md; git -C $S/l -c user.name=x -c user.email=x@x commit -qam x"
run dev-link 1 "mkdir -p .lake/packages; ln -s /home/user/lean-categories .lake/packages/lean_categories"
run intent-edit 1 "echo x >> custodian/owner-intent.md"
run adversarial-edit 1 "echo '# x' >> custodian/adversarial.sh"
run boundary-shrink 1 "python3 -c \"import json;p='custodian/boundary.json';d=json.load(open(p));d['boundary'].remove('CasGates/*');open(p,'w').write(json.dumps(d))\""

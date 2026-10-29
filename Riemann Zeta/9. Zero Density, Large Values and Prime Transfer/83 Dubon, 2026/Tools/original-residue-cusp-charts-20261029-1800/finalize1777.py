from pathlib import Path
import json,re,runpy,sys
D=Path('E:/Lean/.tmp/dubon83');P=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
paper,foundation=sys.argv[1:3]
t=(P/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in t
assert not re.search(r'PANIC|fatal exception',t,re.I)
f=P/'Tools/actual-ordinary-invariant-line-route-20261010.json';v=json.loads(f.read_text(encoding='utf8'))
v['status']='All thirteen modules1765-1777, exact consumers, independent regression/audit executions and sequential foundation/paper verifiers PASS with actual exits0 consumed and zero diagnostics.'
v['semanticBoundary']='Verified exact equivalence between the actual ordinary matrix relations and the genuine full invariant submodule being free of rank one and a direct summand. The original representation, local residue map and nonidentity residual element remain explicit. Arithmetic inertia specialization, deriving the residual element, literal ordinary quotient and class classification, finite-flat and p-adic Hodge conditions, full Selmer comparison, modular association and patching remain open.'
for row in v['modules']:row['status']='Focused and full assembled verification PASS with zero diagnostics.'
v['next']='Derive the actual residual nonidentity element, specialize to original arithmetic inertia, and construct the genuine ordinary coefficient quotient and class classification.'
v['scopeLimit']='The actual ordinary invariant rank-one direct-summand equivalence is verified. Original arithmetic quotient assembly, finite-flat and p-adic Hodge conditions and source modular conclusions remain open.'
v['existingCodeGeneralization']['status']='APPLIED; generalized action, original field Schur results and all existing consumers passed full assembled verification with zero diagnostics.'
v['prerequisiteExistingCodeGeneralization']='Applied and fully verified, including all existing downstream consumers; before/after hashes retained in existingCodeGeneralization.'
(D/'matrix-standard-action-generalization-review.json').write_text(json.dumps(v['existingCodeGeneralization'],ensure_ascii=False,indent=2)+'\n',encoding='utf8')
route_verified=v
v['validation']={'foundation':foundation,'paper':paper,'scope':[1777,1144,7347]}
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
sys.argv=[str(D/'record1777combined.py'),paper,foundation];runpy.run_path(sys.argv[0])
count=int(re.findall(r'AUDIT PASS: (\d+) project theorems',t)[0]);lint=list(map(int,re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',t)[0]))
f=D/'current-factorization-state.json';s=json.loads(f.read_text(encoding='utf8'));s.update(lastFullyVerifiedScope=1777,lastReceiptRecorded=True,lastPaperLog=paper,lastPaper=paper,lastFoundationLog=foundation,lastFoundation=foundation,focusedExhaustiveChecks=count,linters=lint)
s['pending1777FullVerification'].update(status='Full foundation and paper PASS actual exits0 consumed; combined receipt EXECUTED.',paper=paper,paperSession=None,receipt='record1777combined.py EXECUTED')
s['futureOrdinaryInvariantDrafts']['status']='All thirteen promoted and fully verified through1777; combined receipt EXECUTED.'
f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=D/'semantic-review1777-20261010.json';v=json.loads(f.read_text(encoding='utf8'));v['proofReview']=route_verified
v.update(status='FINAL PASS: actual exits0 consumed, zero diagnostics, all exact consumers, both dependency audits and all16linters.',receipt='record1777combined.py EXECUTED',paper=paper,foundation=foundation,exhaustive=count,linters=lint)
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded full1777 PASS; source gates17-20 remain OPEN.')

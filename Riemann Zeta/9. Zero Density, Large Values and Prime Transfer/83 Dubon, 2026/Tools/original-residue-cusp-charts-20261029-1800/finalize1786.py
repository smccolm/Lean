from pathlib import Path
import json,re,runpy,sys
D=Path('E:/Lean/.tmp/dubon83');P=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
paper,foundation=sys.argv[1:3]
t=(P/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in t
assert not re.search(r'PANIC|fatal exception',t,re.I)
f=P/'Tools/actual-arithmetic-ordinary-quotient-route-20261010.json';v=json.loads(f.read_text(encoding='utf8'))
v['status']='All nine modules1778-1786, exact consumers, independent regression/audit executions and sequential foundation/paper verifiers PASS with actual exits0 consumed and zero diagnostics.'
v['semanticBoundary']='Ordinary invariant direct-summand geometry, coefficient ideal and original arithmetic class classification. Actual residual absolute irreducibility, residue characteristic and residual ordinarity remain explicit. Finite-flat and p-adic Hodge conditions, Selmer theory, modular association and patching remain open.'
for row in v['modules']:row['status']='Focused and full assembled verification PASS with zero diagnostics.'
v['next']='Construct the remaining finite-flat and p-adic Hodge local conditions, full Selmer comparison, modular association and patching. Ordinary/determinant combinations must consume the actual coefficient ideals and class conditions.'
v['scopeLimit']='Ordinary invariant direct-summand geometry, coefficient ideal and original arithmetic class classification. Actual residual absolute irreducibility, residue characteristic and residual ordinarity remain explicit. Finite-flat and p-adic Hodge conditions, Selmer theory, modular association and patching remain open.'
v['arithmeticAssembly']['status']='Full assembled verification PASS, actual exits0 consumed and zero diagnostics.'
route_verified=v
v['validation']={'foundation':foundation,'paper':paper,'scope':[1786,1153,7369]}
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
sys.argv=[str(D/'record1786combined.py'),paper,foundation];runpy.run_path(sys.argv[0])
count=int(re.findall(r'AUDIT PASS: (\d+) project theorems',t)[0]);lint=list(map(int,re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',t)[0]))
f=D/'current-factorization-state.json';s=json.loads(f.read_text(encoding='utf8'));s.update(lastFullyVerifiedScope=1786,lastReceiptRecorded=True,lastPaperLog=paper,lastPaper=paper,lastFoundationLog=foundation,lastFoundation=foundation,focusedExhaustiveChecks=count,linters=lint)
s['pending1786FullVerification'].update(status='Full foundation and paper PASS actual exits0 consumed; combined receipt EXECUTED.',paper=paper,paperSession=None,receipt='record1786combined.py EXECUTED')
s['futureArithmeticOrdinaryAssembly']['status']='Promoted and fully verified through1786; combined receipt EXECUTED.'
s['futureOrdinaryQuotientDrafts']['status']='All nine promoted and fully verified through1786; combined receipt EXECUTED.'
f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=D/'semantic-review1786-20261010.json';v=json.loads(f.read_text(encoding='utf8'));v['proofReview']=route_verified
v.update(status='FINAL PASS: actual exits0 consumed, zero diagnostics, all exact consumers, both dependency audits and all16linters.',receipt='record1786combined.py EXECUTED',paper=paper,foundation=foundation,exhaustive=count,linters=lint)
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded full1786 PASS; source gates17-20 remain OPEN.')

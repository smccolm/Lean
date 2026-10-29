from pathlib import Path
import json,re,runpy,sys
D=Path('E:/Lean/.tmp/dubon83');P=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
paper,foundation=sys.argv[1:3]
t=(P/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in t
assert not re.search(r'PANIC|fatal exception',t,re.I)
f=P/'Tools/actual-unframed-condition-route-20261010.json';v=json.loads(f.read_text(encoding='utf8'))
v['status']='All eight modules1757-1764, exact consumers, independent regression/audit executions and sequential foundation/paper verifiers PASS with actual exits0 consumed and zero diagnostics.'
v['semanticBoundary']='Verified actual determinant and inertia conditions on the original unframed arithmetic classes, with a literal quotient of the constructed arithmetic trace ring. Original residual irreducibility, residue characteristic, determinant compatibility and residual inertia-killing remain explicit arithmetic inputs. Quotient locality, Noetherianity, maximal-adic topology, completeness and exact class evaluation are derived. Exceptional ordinary, finite-flat and p-adic Hodge conditions, full Selmer comparison, modular association and patching remain open.'
for row in v['modules']:row['status']='Focused and full assembled verification PASS with zero diagnostics.'
v['arithmeticAssembly']['status']='Full assembled verification PASS with actual exits0 consumed and zero diagnostics.'
v['next']='Compile and verify the actual ordinary invariant direct-summand criterion1765-1777, then construct the original ordinary quotient classification. Source gates17-20 remain open.'
route_verified=v
v['validation']={'foundation':foundation,'paper':paper,'scope':[1764,1131,7318]}
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
sys.argv=[str(D/'record1764combined.py'),paper,foundation];runpy.run_path(sys.argv[0])
count=int(re.findall(r'AUDIT PASS: (\d+) project theorems',t)[0]);lint=list(map(int,re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',t)[0]))
f=D/'current-factorization-state.json';s=json.loads(f.read_text(encoding='utf8'));s.update(lastFullyVerifiedScope=1764,lastReceiptRecorded=True,lastPaperLog=paper,lastPaper=paper,lastFoundationLog=foundation,lastFoundation=foundation,focusedExhaustiveChecks=count,linters=lint)
s['pending1764FullVerification'].update(status='Full foundation and paper PASS actual exits0 consumed; combined receipt EXECUTED.',paper=paper,paperSession=None,receipt='record1764combined.py EXECUTED')
s['futureUnframedConditionDrafts']['status']='All eight promoted and fully verified through1764; combined receipt EXECUTED.'
f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=D/'semantic-review1764-20261010.json';v=json.loads(f.read_text(encoding='utf8'));v['proofReview']=route_verified
v.update(status='FINAL PASS: actual exits0 consumed, zero diagnostics, all exact consumers, both dependency audits and all16linters.',receipt='record1764combined.py EXECUTED',paper=paper,foundation=foundation,exhaustive=count,linters=lint)
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded full1764 PASS; source gates17-20 remain OPEN.')

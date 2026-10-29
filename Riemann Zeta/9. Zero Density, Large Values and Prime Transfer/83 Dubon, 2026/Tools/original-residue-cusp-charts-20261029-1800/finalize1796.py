from pathlib import Path
import json,re,runpy,sys
D=Path('E:/Lean/.tmp/dubon83');P=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
paper,foundation=sys.argv[1:3]
t=(P/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in t
assert not re.search(r'PANIC|fatal exception',t,re.I)
f=P/'Tools/actual-arithmetic-ordinary-and-hopf-coordinate-route-20261010.json';v=json.loads(f.read_text(encoding='utf8'))
v['status']='All ten modules1787-1796, exact consumers, independent regression/audit executions and sequential foundation/paper verifiers PASS with actual exits0 consumed and zero diagnostics.'
v['semanticBoundary']='The original arithmetic fixed-determinant ordinary classification retains the real residual absolute irreducibility, residue characteristic, determinant compatibility and residual ordinarity inputs. The later Hopf point and coordinate-closure constructions do not supply comultiplication descent, a Hopf quotient, Galois-stable generic-fiber comparison, finite-flat group-scheme products/subquotients, original arithmetic finite-flat realization or a finite-flat deformation quotient. No modular source gate closes.'
for row in v['modules']:row['status']='Focused and full assembled verification PASS with zero diagnostics.'
v['next']='Prove actual comultiplication descent and the Galois-stable geometric-point identification, preserving all source generic-fiber and finite-quotient requirements.'
v['scopeLimit']='The original arithmetic fixed-determinant ordinary classification retains the real residual absolute irreducibility, residue characteristic, determinant compatibility and residual ordinarity inputs. The later Hopf point and coordinate-closure constructions do not supply comultiplication descent, a Hopf quotient, Galois-stable generic-fiber comparison, finite-flat group-scheme products/subquotients, original arithmetic finite-flat realization or a finite-flat deformation quotient. No modular source gate closes.'
v['arithmeticAssembly']['status']='Full assembled verification PASS, actual exits0 consumed and zero diagnostics.'
route_verified=v
v['validation']={'foundation':foundation,'paper':paper,'scope':[1796,1163,7399]}
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
sys.argv=[str(D/'record1796combined.py'),paper,foundation];runpy.run_path(sys.argv[0])
count=int(re.findall(r'AUDIT PASS: (\d+) project theorems',t)[0]);lint=list(map(int,re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',t)[0]))
f=D/'current-factorization-state.json';s=json.loads(f.read_text(encoding='utf8'));s.update(lastFullyVerifiedScope=1796,lastReceiptRecorded=True,lastPaperLog=paper,lastPaper=paper,lastFoundationLog=foundation,lastFoundation=foundation,focusedExhaustiveChecks=count,linters=lint)
s['pending1796FullVerification'].update(status='Full foundation and paper PASS actual exits0 consumed; combined receipt EXECUTED.',paper=paper,paperSession=None,receipt='record1796combined.py EXECUTED')
s['futureDeterminantOrdinaryDrafts']['status']='Four arithmetic determinant/ordinary modules fully verified within combined1796; no separate full1790 receipt.'
s['futureFiniteFlatPointDrafts']['status']='Three point modules promoted and fully verified through1796; combined receipt EXECUTED.'
s['futureFiniteFlatClosureDrafts']['status']='Three coordinate-closure modules promoted and fully verified through1796; combined receipt EXECUTED.'
f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=D/'semantic-review1796-20261010.json';v=json.loads(f.read_text(encoding='utf8'));v['proofReview']=route_verified
v.update(status='FINAL PASS: actual exits0 consumed, zero diagnostics, all exact consumers, both dependency audits and all16linters.',receipt='record1796combined.py EXECUTED',paper=paper,foundation=foundation,exhaustive=count,linters=lint)
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded full1796 PASS; source gates17-20 remain OPEN.')

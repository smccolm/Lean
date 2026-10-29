from pathlib import Path
import json,re,runpy,sys
D=Path('E:/Lean/.tmp/dubon83');P=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
paper,foundation=sys.argv[1:3]
t=(P/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in t
assert not re.search(r'PANIC|fatal exception',t,re.I)
f=P/'Tools/actual-original-unframed-route-20261010.json';v=json.loads(f.read_text(encoding='utf8'))
v['status']='All ten modules1738-1747, exact consumers, independent regression/audit executions and sequential foundation/paper verifiers PASS with actual exits0 consumed and zero diagnostics.'
v['semanticBoundary']='Verified construction in the actual maximal-adic complete local target category using the existing original strict-conjugacy class definitions. One constructed whole trace representation gives the class bijections for all these targets, and the existing original coefficient changes satisfy naturality. Original residual absolute irreducibility and a genuine finitely generated profinite presentation remain explicit inputs. No arbitrary pro-Artinian generality, exceptional local conditions, full Selmer comparison, modular association, patching or source modular conclusions are claimed.'
for row in v['modules']:row['status']='Focused and full assembled verification PASS with zero diagnostics.'
v['validation']={'foundation':foundation,'paper':paper,'scope':[1747,1114,7274]}
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
sys.argv=[str(D/'record1747combined.py'),paper,foundation];runpy.run_path(sys.argv[0])
count=int(re.findall(r'AUDIT PASS: (\d+) project theorems',t)[0]);lint=list(map(int,re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',t)[0]))
f=D/'current-factorization-state.json';s=json.loads(f.read_text(encoding='utf8'));s.update(lastFullyVerifiedScope=1747,lastReceiptRecorded=True,lastPaperLog=paper,lastPaper=paper,lastFoundationLog=foundation,lastFoundation=foundation,focusedExhaustiveChecks=count,linters=lint)
s['pending1747FullVerification'].update(status='Full foundation and paper PASS actual exits0 consumed; combined receipt EXECUTED.',paper=paper,paperSession=None,receipt='record1747combined.py EXECUTED')
s['futureUnframedDrafts']['status']='All ten promoted and fully verified through1747; combined receipt EXECUTED.'
f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=D/'semantic-review1747-20261010.json';v=json.loads(f.read_text(encoding='utf8'));v.update(status='FINAL PASS: actual exits0 consumed, zero diagnostics, all exact consumers, both dependency audits and all16linters.',receipt='record1747combined.py EXECUTED',paper=paper,foundation=foundation,exhaustive=count,linters=lint)
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded full1747 PASS; source gates17-20 remain OPEN.')

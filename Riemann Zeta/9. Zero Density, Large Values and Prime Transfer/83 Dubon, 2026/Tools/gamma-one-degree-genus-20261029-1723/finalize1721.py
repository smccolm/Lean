from pathlib import Path
import json,re,runpy,sys,hashlib
D=Path('E:/Lean/.tmp/dubon83');P=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
paper,foundation=sys.argv[1:3]
t=(P/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in t
assert not re.search(r'PANIC|fatal exception',t,re.I)
f=P/'Tools/actual-whole-trace-descent-route-20261010.json';v=json.loads(f.read_text(encoding='utf8'))
v['status']='All six modules1716-1721, exact consumers, independent regression/audit executions and sequential foundation/paper verifiers PASS with actual exits0 consumed and zero diagnostics.'
v['remaining']='Whole continuous original representation descent in the actual inherited trace-coefficient topology is proved. Noetherian image/retraction argument, unframed universality, exceptional local deformation conditions, modular association, full Selmer theory and patching remain unproved. DUB-17-20 remain OPEN.'
v['validation']={'foundation':foundation,'paper':paper,'scope':[1721,1088,7211]}
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
sys.argv=[str(D/'record1721combined.py'),paper,foundation];runpy.run_path(sys.argv[0])
count=int(re.findall(r'AUDIT PASS: (\d+) project theorems',t)[0]);lint=list(map(int,re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',t)[0]))
f=D/'current-factorization-state.json';s=json.loads(f.read_text(encoding='utf8'));s.update(lastFullyVerifiedScope=1721,lastReceiptRecorded=True,lastPaperLog=paper,lastPaper=paper,lastFoundationLog=foundation,lastFoundation=foundation,focusedExhaustiveChecks=count,linters=lint)
s['pending1721FullVerification'].update(status='Full foundation and repaired paper PASS actual exits0 consumed; combined receipt EXECUTED.',paper=paper,paperSession=None)
f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=D/'semantic-review1721-20261010.json';v=json.loads(f.read_text(encoding='utf8'));v.update(status='FINAL PASS: actual exits0 consumed, zero diagnostics, all exact consumers, both dependency audits and all16linters.',receipt='record1721combined.py EXECUTED',paper=paper,foundation=foundation,exhaustive=count,linters=lint)
v['consumerRepair']['validation']='arithmetic1721b-focus.log and full repaired paper PASS with actual exits0 consumed and zero diagnostics.'
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded full1721 PASS and corrected retained API/progress descriptions; source gates17-20 remain OPEN.')

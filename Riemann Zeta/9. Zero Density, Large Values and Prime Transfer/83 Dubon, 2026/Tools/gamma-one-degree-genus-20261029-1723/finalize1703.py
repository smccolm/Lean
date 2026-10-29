from pathlib import Path
import json,re,runpy,sys,hashlib
D=Path('E:/Lean/.tmp/dubon83');P=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
paper=sys.argv[1];foundation='../../logs/foundation_freeze_20261010_054130.log'
t=(P/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in t
assert not re.search(r'PANIC|fatal exception',t,re.I)
f=P/'Tools/actual-original-trace-basis-route-20261010.json';v=json.loads(f.read_text(encoding='utf8'))
v['status']='All nine modules1695-1703, exact consumers, independent regression/audit executions and sequential foundation/paper verifiers PASS with actual exits0 consumed and zero diagnostics.'
v['exactPinnedApis']=[s.replace('LinearIndependent.span','Module.Basis.span') for s in v['exactPinnedApis']]
v['remaining']='Converge the actual idempotent iteration inside the proved actual finite free closed representation matrix algebra; construct the original-dimensional left ideal and residue-identity change of basis; prove continuity and descent of the whole original representation. Noetherian image/retraction argument, unframed universality, exceptional local deformation conditions, modular association, full Selmer theory and patching remain unproved. DUB-17-20 remain OPEN.'
v['validation']={'foundation':foundation,'paper':paper,'scope':[1703,1070,7159]}
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
sys.argv=[str(D/'record1703combined.py'),paper,foundation];runpy.run_path(sys.argv[0])
count=int(re.findall(r'AUDIT PASS: (\d+) project theorems',t)[0]);lint=list(map(int,re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',t)[0]))
f=D/'current-factorization-state.json';s=json.loads(f.read_text(encoding='utf8'));s.update(lastFullyVerifiedScope=1703,lastReceiptRecorded=True,lastPaperLog=paper,lastPaper=paper,lastFoundationLog=foundation,lastFoundation=foundation,focusedExhaustiveChecks=count,linters=lint)
s['pending1703FullVerification'].update(status='Full foundation and repaired paper PASS actual exits0 consumed; combined receipt EXECUTED.',paper=paper,paperSession=None)
f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=D/'semantic-review1703-20261010.json';v=json.loads(f.read_text(encoding='utf8'));v.update(status='FINAL PASS: actual exits0 consumed, zero diagnostics, all exact consumers, both dependency audits and all16linters.',receipt='record1703combined.py EXECUTED',paper=paper,foundation=foundation,exhaustive=count,linters=lint)
v['consumerRepair']['validation']='arithmetic1703b-focus.log clean PASS and full paper rerun PASS, actual exits0 consumed.'
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded full1703 PASS and corrected retained API/progress descriptions; source gates17-20 remain OPEN.')

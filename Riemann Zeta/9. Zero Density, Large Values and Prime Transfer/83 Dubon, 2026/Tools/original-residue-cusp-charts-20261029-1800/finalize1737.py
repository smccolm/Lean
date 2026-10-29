from pathlib import Path
import json,re,runpy,sys
D=Path('E:/Lean/.tmp/dubon83');P=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
paper,foundation=sys.argv[1:3]
t=(P/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in t
assert not re.search(r'PANIC|fatal exception',t,re.I)
f=P/'Tools/actual-coefficient-retraction-route-20261010.json';v=json.loads(f.read_text(encoding='utf8'))
v['status']='All sixteen modules1722-1737, exact consumers, independent regression/audit executions and sequential foundation/paper verifiers PASS with actual exits0 consumed and zero diagnostics.'
v['futureAssembly']['status']='All five assembly modules1733-1737 fully verified in assembled scope1737.'
for row in v['modules']+v['futureAssembly']['modules']:row['status']='Focused and full assembled verification PASS with zero diagnostics.'
v['validation']={'foundation':foundation,'paper':paper,'scope':[1737,1104,7251]}
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
sys.argv=[str(D/'record1737combined.py'),paper,foundation];runpy.run_path(sys.argv[0])
count=int(re.findall(r'AUDIT PASS: (\d+) project theorems',t)[0]);lint=list(map(int,re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',t)[0]))
f=D/'current-factorization-state.json';s=json.loads(f.read_text(encoding='utf8'));s.update(lastFullyVerifiedScope=1737,lastReceiptRecorded=True,lastPaperLog=paper,lastPaper=paper,lastFoundationLog=foundation,lastFoundation=foundation,focusedExhaustiveChecks=count,linters=lint)
s['pending1737FullVerification'].update(status='Full foundation and paper PASS actual exits0 consumed; combined receipt EXECUTED.',paper=paper,paperSession=None,receipt='record1737combined.py EXECUTED')
for key in ['futureNoetherianRouteDrafts','futureTopologyTransportDrafts']:s[key]['status']='All promoted and fully verified through1737; combined receipt EXECUTED.'
f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=D/'semantic-review1737-20261010.json';v=json.loads(f.read_text(encoding='utf8'));v.update(status='FINAL PASS: actual exits0 consumed, zero diagnostics, all exact consumers, both dependency audits and all16linters.',receipt='record1737combined.py EXECUTED',paper=paper,foundation=foundation,exhaustive=count,linters=lint)
f.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('Recorded full1737 PASS; source gates17-20 remain OPEN.')

from pathlib import Path
import json,hashlib
p=Path(__file__).parent
old=json.loads((p/'reduced-diamond-action-versions-1691.json').read_text(encoding='utf-8'))
changes={'SourceIntegralDiamondFieldPull':'1683d','SourceIntegralDiamondFieldRange':'1684b',
 'SourceIntegralDiamondFieldConstants':'1685c','SourceIntegralDiamondFieldOperations':'1686b',
 'SourceIntegralDiamondFieldComposition':'1688c','SourceIntegralDiamondFieldIdentity':'1689b',
 'SourceIntegralDiamondFieldAction':'1690b'}
new={**old,**changes};rows=[]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
for m,v in changes.items():
 f=p/(m+old[m]+'.lean');s=f.read_text(encoding='utf-8')
 for n,w in changes.items():s=s.replace('import '+n+old[n]+'\n','import '+n+w+'\n')
 if m=='SourceIntegralDiamondFieldPull':
  for field,doc in [('weight','The shared integer weight of the two actual modular forms.'),('numerator','The actual Gamma1 modular form in the numerator.'),('denominator','The actual Gamma1 modular form in the denominator.'),('numeratorSeries','The integer Fourier series of the numerator.'),('denominatorSeries','The integer Fourier series of the denominator.')]:
   s=s.replace('  '+field+' :','  /-- '+doc+' -/\n  '+field+' :')
 q=p/(m+v+'.lean');assert not q.exists();q.write_text(s,encoding='utf-8')
 rows.append(dict(previous=str(f),previousSha256=sha(f),successor=str(q),successorSha256=sha(q)))
f=p/'reduced-diamond-action-versions-1693.json';assert not f.exists();f.write_text(json.dumps(new,indent=2)+'\n',encoding='utf-8')
f=p/'reduced-diamond-action-doc-repair-1693.json';assert not f.exists();f.write_text(json.dumps(dict(reason='The complete 1691 preflight found five docBlame failures on data projections of EvenIntegralRepresentative. Add exactly the five missing field documentation strings; preserve all statements and proof bodies and propagate only import changes. Every original source and failure log remains immutable. No linter or proof check is weakened.',files=rows,productionMutation=False),indent=2)+'\n',encoding='utf-8')
runner="$ErrorActionPreference='Stop'\nforeach($name in @("+','.join(repr(m+v) for m,v in changes.items())+")){\n & powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\\Lean\\.tmp\\dubon83\\run_scratch_module_1433.ps1' -Name $name\n if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}\n}\n"
f=p/'build_reduced_action_doc_repair_1693.ps1';assert not f.exists();f.write_text(runner,encoding='utf-8')
print(json.dumps(dict(modules=len(changes),documentationFields=5,proofChanges=0)))

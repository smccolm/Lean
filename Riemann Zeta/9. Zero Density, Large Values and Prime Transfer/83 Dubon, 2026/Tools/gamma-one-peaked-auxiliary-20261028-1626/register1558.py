from pathlib import Path
import json,re
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
f=p/'Tools/scaffold.json';s=json.loads(f.read_text(encoding='utf8'));assert len(s['productionModules'])==1557
modules=sorted(q.stem for q in (p/'Extension/Dubon2026').glob('*.lean') if q.stem not in s['productionModules'] and q.stem not in ['Audit','SemanticRegression'])
assert len(modules)==1
new=[]
for n in modules:
 t=(p/f'Extension/Dubon2026/{n}.lean').read_text(encoding='utf8')
 new+=['Dubon2026.'+x for x in re.findall(r"^(?:theorem|lemma)\s+([\w']+)",t,re.M)]
 s['productionModules'].append(n);s['files'].append({'path':f'Extension/Dubon2026/{n}.lean','role':'Extension'})
s['files'].sort(key=lambda x:x['path']);f.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=p/'Extension/Dubon2026.lean';t=f.read_text(encoding='utf8');f.write_text(t+''.join('import Dubon2026.'+n+'\n' for n in modules),encoding='utf8')
f=p/'Extension/Dubon2026/SemanticRegression.lean';t=f.read_text(encoding='utf8');c=(d/'consumers1558.txt').read_text(encoding='utf8');assert c not in t
f.write_text(t.replace('end Dubon2026.SemanticRegression',c+'end Dubon2026.SemanticRegression'),encoding='utf8')
new+=['Dubon2026.SemanticRegression.'+x for x in re.findall(r"^theorem\s+([\w']+)",c,re.M)]
f=p/'Extension/Dubon2026/Audit.lean';t=f.read_text(encoding='utf8');anchor='\n]\n\nprivate def runAudit';assert anchor in t
old=len(re.findall(r'``Dubon2026\.',t));assert old==6668,old
t=t.replace(anchor,',\n'+',\n'.join('  ``'+n for n in new)+anchor);f.write_text(t,encoding='utf8')
f=p/'Tools/proof_gates.json';gates=json.loads(f.read_text(encoding='utf8'));g=next(g for g in gates['gates'] if g['id']=='DUB-17');g['implementationFiles'] += [f'Extension/Dubon2026/{n}.lean' for n in modules];f.write_text(json.dumps(gates,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
(d/'modules1558.json').write_text(json.dumps(modules,indent=2)+'\n',encoding='utf8')
(d/'registrations1558.json').write_text(json.dumps(new,indent=2)+'\n',encoding='utf8')
print(f'Registered 1558 modules / 925 exact consumers / {old+len(new)} explicit audit declarations; added {len(new)} theorems.')

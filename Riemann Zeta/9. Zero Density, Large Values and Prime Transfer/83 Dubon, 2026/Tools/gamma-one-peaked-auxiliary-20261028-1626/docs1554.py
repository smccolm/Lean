from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1554.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1554.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual unramified compositum integral closure: '+math+' One exact consumer expands registered scope to 1554 production modules, 921 exact consumers and 6,661 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1554.json').read_text(encoding='utf8'))
section='### Actual unramified compositum integral closure — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1554.txt').write_text(status+'\n',encoding='utf8');(d/'section1554.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1554
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  CLIA --> LCL';assert old in t
new=old+'\n  TCI --> UCI["Proved actual integral closure in the original field compositum is unramified"]\n  UCI --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualUnramifiedCompositumIntegralClosureImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1554 production modules, 921 exact consumers and 6661 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualUnramifiedCompositumIntegralClosurePrimaryRecheck20261009']=json.loads((d/'primary-review1554.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='The original arithmetic Galois extension and its ramification hypotheses, its required cyclotomic intermediate field, the all-open-subgroup Mazur condition, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='The actual tensor image of finite unramified algebras is now the integral closure in the original generated field compositum, and uniqueness of that actual integral closure transfers formal unramifiedness (focused compilation passed; expanded verification pending). The original arithmetic Galois extension and its ramification hypotheses, its required cyclotomic intermediate field, the all-open-subgroup Mazur condition, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual unramified compositum integral closure; 1554 modules / 921 consumers / 6661 registrations.')

from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1540.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1540.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual unramified localizations and tensor images: '+math+' Two exact consumers expand registered scope to 1540 production modules, 907 exact consumers and 6,620 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1540.json').read_text(encoding='utf8'))
section='### Actual unramified localizations and tensor images — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1540.txt').write_text(status+'\n',encoding='utf8');(d/'section1540.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1540
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  FBU --> LCL';assert old in t
new='  FBU --> LCL\n  NRU["Proved original number-field index-one and unramified-localization equivalence"] --> LCL\n  UTI["Proved genuine finite unramified tensor images are Dedekind domains"] --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualUnramifiedTensorImageImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1540 production modules, 907 exact consumers and 6620 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualUnramifiedTensorImagePrimaryRecheck20261009']=json.loads((d/'primary-review1540.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='The original arithmetic Galois extension and its ramification hypotheses, its required cyclotomic intermediate field, the all-open-subgroup Mazur condition, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='The original number-field prime index is now linked to its genuine unramified localization, and actual tensor images of finite unramified algebras inside the original ambient field are proved finite unramified Dedekind domains and integral closures in their actual fields of fractions (focused compilation passed; expanded verification pending). The original arithmetic Galois extension and its ramification hypotheses, its required cyclotomic intermediate field, the all-open-subgroup Mazur condition, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual unramified localizations and tensor images; 1540 modules / 907 consumers / 6620 registrations.')

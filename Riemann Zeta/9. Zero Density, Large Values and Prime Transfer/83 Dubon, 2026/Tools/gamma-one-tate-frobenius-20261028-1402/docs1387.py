from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1387.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1387.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original representation determinant family and tensor extension: '+math+' Seven exact consumers expand registered scope to 1387 production modules, 754 exact consumers and 6,077 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1387.json').read_text(encoding='utf8'))
section='### Original representation determinant family and tensor extension — 8 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1387.txt').write_text(status+'\n',encoding='utf8');(d/'section1387.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1387
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  ASC --> LCL';assert old in t
new='  ASC --> DTL["Proved actual representation determinant family, coefficient naturality and original tensor/characteristic identities"]\n  DTL --> LCL'
t=t.replace(old,new,1).replace('OPEN DUB-17: standard unramified induced representation identification and full automorphic Euler interpretation','OPEN DUB-17: higher symmetric automorphic lifts and continuation of the actual Euler functions')
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['matrixDeterminantLawImplementation20261008']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1387 production modules, 754 exact consumers and 6077 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['matrixDeterminantPrimaryRecheck20261008']=json.loads((d/'primary-review1387.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='These arithmetic representation operations do not construct associated Galois representations or higher automorphic lifts.'
 assert anchor in t
 extra=' The actual representation determinant family, arbitrary-group tensor-extension equivalence and original characteristic-polynomial identities are constructed (focused compilation passed; expanded verification pending). Galois association, pseudodeformation representability and automorphy lifting remain open.'
 q.write_text(t.replace(anchor,anchor+extra,1),encoding='utf8')

print('Synchronized original representation determinant family; 1387 modules / 754 consumers / 6077 registrations.')

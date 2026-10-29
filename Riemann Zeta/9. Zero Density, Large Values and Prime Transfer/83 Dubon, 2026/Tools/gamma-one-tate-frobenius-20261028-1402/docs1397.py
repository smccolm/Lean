from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1397.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1397.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original first-order matrix lifts and actual adjoint cocycles: '+math+' Four exact consumers expand registered scope to 1397 production modules, 764 exact consumers and 6,109 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1397.json').read_text(encoding='utf8'))
section='### Original first-order matrix lifts and actual adjoint cocycles — 8 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1397.txt').write_text(status+'\n',encoding='utf8');(d/'section1397.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1397
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  NDL --> LCL';assert old in t
new='  NDL --> FOC["Proved actual dual-number lifts and exact original adjoint cocycle equivalence"]\n  FOC --> LCL'
t=t.replace(old,new,1).replace('OPEN DUB-17: standard unramified induced representation identification and full automorphic Euler interpretation','OPEN DUB-17: higher symmetric automorphic lifts and continuation of the actual Euler functions')
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['firstOrderAdjointDeformationImplementation20261008']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1397 production modules, 764 exact consumers and 6109 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['firstOrderAdjointPrimaryRecheck20261008']=json.loads((d/'primary-review1397.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Galois association, pseudodeformation representability and automorphy lifting remain open.'
 assert anchor in t
 extra=' The genuine first-order lift fiber over the dual numbers is identified with Mathlib’s actual adjoint cocycle module, using the original reduction and explicit inverse matrix constructions (focused compilation passed; expanded verification pending). Strict-conjugacy/cohomology and continuous deformation conditions remain separate obligations.'
 q.write_text(t.replace(anchor,anchor+extra,1),encoding='utf8')

print('Synchronized original representation determinant family; 1397 modules / 764 consumers / 6109 registrations.')

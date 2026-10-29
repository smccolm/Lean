from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1429.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1429.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original symmetric adjoint cohomology and actual local residual points: '+math+' Four exact consumers expand registered scope to 1429 production modules, 796 exact consumers and 6,231 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1429.json').read_text(encoding='utf8'))
section='### Original symmetric adjoint cohomology and actual local residual points — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1429.txt').write_text(status+'\n',encoding='utf8');(d/'section1429.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1429
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  TAN --> LCL';assert old in t
new='  TAN --> SYH["Proved actual linear symmetric adjoint H1 and original residual point kernels and units"]\n  RCA --> SYH\n  SYH --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['symmetricCohomologyResidualPointImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1429 production modules, 796 exact consumers and 6231 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['symmetricCohomologyResidualPointPrimaryRecheck20261009']=json.loads((d/'primary-review1429.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Linear symmetric H1 descent, profinite complete local and pseudodeformation representability, Galois-specific local conditions and Selmer inputs remain open.'
 assert anchor in t
 extra='The actual symmetric tangent map now descends linearly to original adjoint H1 with the exact class of every original symmetric first-order lift. The genuine residual representation point over a local coefficient ring has its actual residue-field quotient, and original integral lifts invert its complement (focused compilation passed; expanded verification pending). Localization, completion, profinite deformation representability, Galois-specific local conditions and Selmer inputs remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual symmetric H1 and residual points; 1429 modules / 796 consumers / 6231 registrations.')

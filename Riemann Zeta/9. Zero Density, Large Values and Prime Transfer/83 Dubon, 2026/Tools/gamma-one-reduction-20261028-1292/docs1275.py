from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1275.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1275.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original full orthogonal compact-type admissibility: '+math+' Nine exact consumers expand registered scope to 1275 production modules, 637 exact consumers and 5,609 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1275.json').read_text(encoding='utf8'))
section='### Original full orthogonal compact-type admissibility — 8 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1275.txt').write_text(status+'\n',encoding='utf8');(d/'section1275.txt').write_text(section,encoding='utf8');(d/'remaining1275.txt').write_text(remaining,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8');old='  IWA --> LCL["OPEN DUB-17: general compact-type identification and spherical Euler classification"]';assert old in t
new='  IWA --> OTA["Proved full orthogonal compact-type finite multiplicity at every original open finite adelic level"]\n  OTA --> LCL["OPEN DUB-17: spherical representation and Euler-factor classification"]';f.write_text(t.replace(old,new,1),encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['adelicOrthogonalTypeAdmissibilityImplementation20261008']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1275 production modules, 637 exact consumers and 5609 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining};f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8');old='The general compact-type formulation, spherical representation/Euler classification, the automorphic non-CM bridge and higher symmetric continuations still require proofs.';assert old in t
 new='The full orthogonal compact-type formulation is now proved for every finite-dimensional complex type and every open finite adelic level, via the actual rotation spectrum and Cayley–Hamilton (focused compilation passed; expanded verification pending). Spherical representation/Euler classification, the automorphic non-CM bridge and higher symmetric continuations still require proofs.'
 q.write_text(t.replace(old,new,1),encoding='utf8')
print('Synchronized original full orthogonal compact-type admissibility; 1275 modules / 637 consumers / 5609 registrations.')

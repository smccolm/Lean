from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1425.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1425.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original tangent linearity, adjoint classes and symmetric lift compatibility: '+math+' Four exact consumers expand registered scope to 1425 production modules, 792 exact consumers and 6,218 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1425.json').read_text(encoding='utf8'))
section='### Original tangent linearity, adjoint classes and symmetric lift compatibility — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1425.txt').write_text(status+'\n',encoding='utf8');(d/'section1425.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1425
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  COT --> LCL';assert old in t
new='  COT --> LCL\n  CFD --> TAN["Proved genuine coordinate tangent linearity, adjoint H1 projection and symmetric-power lift compatibility"]\n  FSP --> TAN\n  TAN --> LCL'
t=t.replace(old,new,1).replace('OPEN DUB-17: standard unramified induced representation identification and full automorphic Euler interpretation','OPEN DUB-17: higher symmetric automorphic lifts and continuation of the actual Euler functions')
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['coordinateTangentLinearitySymmetricImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1425 production modules, 792 exact consumers and 6218 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['coordinateTangentLinearitySymmetricPrimaryRecheck20261009']=json.loads((d/'primary-review1425.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Profinite complete local and pseudodeformation representability, Galois-specific local conditions and Selmer inputs remain open.'
 assert anchor in t
 extra=' The original coordinate derivation/cocycle correspondence is now proved linear by its literal epsilon-matrix formula, with a genuine surjective linear projection to actual adjoint H1. The actual symmetric coordinate derivative map recovers the entire original symmetric-power first-order lift (focused compilation passed; expanded verification pending). Linear symmetric H1 descent, profinite complete local and pseudodeformation representability, Galois-specific local conditions and Selmer inputs remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual tangent linearity and symmetric lift compatibility; 1425 modules / 792 consumers / 6218 registrations.')

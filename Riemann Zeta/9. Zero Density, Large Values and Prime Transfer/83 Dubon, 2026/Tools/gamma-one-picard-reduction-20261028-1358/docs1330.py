from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1330.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1330.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original integral-idele quadratic Dirichlet descent: '+math+' Eight exact consumers expand registered scope to 1330 production modules, 693 exact consumers and 5,835 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1330.json').read_text(encoding='utf8'))
section='### Original integral-idele quadratic Dirichlet descent — 8 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1330.txt').write_text(status+'\n',encoding='utf8');(d/'section1330.txt').write_text(section,encoding='utf8');(d/'remaining1330.txt').write_text(remaining,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  DST --> NCB["OPEN DUB-17: classification of all relevant automorphic quadratic characters and primitive descent"]';assert old in t
new='  DST --> NCB["OPEN DUB-17: full idele reconstruction, primitive character descent and complete non-CM consumption"]\n  ICD["Proved continuous quadratic integral-idele Dirichlet descent via actual positive congruence modulus"] --> NCB\n  IRC["Proved actual full idele coordinates and real quadratic sign classification"] --> NCB'
f.write_text(t.replace(old,new,1),encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['integralIdeleDirichletDescentImplementation20261008']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1330 production modules, 693 exact consumers and 5835 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining};f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8');old='Standard unramified induced representation identification and full automorphic Euler interpretation, classification of all relevant automorphic quadratic characters and primitive descent, and higher symmetric continuations still require proofs.';assert old in t
 new='Every actual continuous quadratic integral-idele character now has proved Dirichlet descent through a positive residue modulus; the genuine full idele coordinates and real quadratic sign classification are also proved (focused compilation passed; expanded verification pending). Standard unramified induced representation identification and full automorphic Euler interpretation, full idele character reconstruction and primitive descent for the complete non-CM bridge, and higher symmetric continuations still require proofs.'
 q.write_text(t.replace(old,new,1),encoding='utf8')
print('Synchronized original integral-idele quadratic Dirichlet descent; 1330 modules / 693 consumers / 5835 registrations.')

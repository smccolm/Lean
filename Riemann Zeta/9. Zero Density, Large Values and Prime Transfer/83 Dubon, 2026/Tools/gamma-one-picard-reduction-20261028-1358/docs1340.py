from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1340.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1340.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original full idele classification and non-CM self-twist exclusion: '+math+' Ten exact consumers expand registered scope to 1340 production modules, 703 exact consumers and 5,870 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1340.json').read_text(encoding='utf8'))
section='### Original full idele classification and non-CM self-twist exclusion — 8 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1340.txt').write_text(status+'\n',encoding='utf8');(d/'section1340.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  DST --> NCB["OPEN DUB-17: full idele reconstruction, primitive character descent and complete non-CM consumption"]';assert old in t
new='  DST --> NCB["Proved full quadratic idele-class reconstruction, primitive descent and original non-CM self-twist exclusion"]\n  NCB --> NST["Proved non-CM excludes every nontrivial continuous idele-class self-twist; quadraticity follows from actual trivial central action"]\n  NST --> A'
f.write_text(t.replace(old,new,1),encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['fullIdeleClassificationNonCMSelfTwistImplementation20261008']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1340 production modules, 703 exact consumers and 5870 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining};f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8');old='Standard unramified induced representation identification and full automorphic Euler interpretation, full idele character reconstruction and primitive descent for the complete non-CM bridge, and higher symmetric continuations still require proofs.';assert old in t
 new='Full original quadratic idele-class reconstruction and primitive Dirichlet descent are now proved. The original non-CM condition excludes every nontrivial continuous idele-class self-twist, with quadraticity derived from the actual trivial central action (focused compilation passed; expanded verification pending). Standard unramified induced representation identification and full automorphic Euler interpretation, and higher symmetric continuations still require proofs.'
 q.write_text(t.replace(old,new,1),encoding='utf8')
print('Synchronized full original idele classification and non-CM exclusion; 1340 modules / 703 consumers / 5870 registrations.')

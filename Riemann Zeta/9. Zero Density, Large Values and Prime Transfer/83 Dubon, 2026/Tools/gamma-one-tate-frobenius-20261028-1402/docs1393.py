from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1393.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1393.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original natural determinant law, basis independence and direct coefficient continuity: '+math+' Four exact consumers expand registered scope to 1393 production modules, 760 exact consumers and 6,098 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1393.json').read_text(encoding='utf8'))
section='### Original natural determinant law, basis independence and direct coefficient continuity — 8 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1393.txt').write_text(status+'\n',encoding='utf8');(d/'section1393.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1393
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  DTL --> LCL';assert old in t
new='  DTL --> NDL["Proved genuine natural determinant law, original basis independence and direct continuity of all tuple coefficients"]\n  NDL --> LCL'
t=t.replace(old,new,1).replace('OPEN DUB-17: standard unramified induced representation identification and full automorphic Euler interpretation','OPEN DUB-17: higher symmetric automorphic lifts and continuation of the actual Euler functions')
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['naturalDeterminantLawImplementation20261008']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1393 production modules, 760 exact consumers and 6098 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['naturalDeterminantPrimaryRecheck20261008']=json.loads((d/'primary-review1393.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Galois association, pseudodeformation representability and automorphy lifting remain open.'
 assert anchor in t
 extra=' The genuine natural determinant-law structure is constructed from the original representations; original changes of basis preserve the whole law, coefficient reduction commutes with it, and all finite-tuple determinant coefficients are proved continuous directly (focused compilation passed; expanded verification pending).'
 q.write_text(t.replace(anchor,anchor+extra,1),encoding='utf8')

print('Synchronized original representation determinant family; 1393 modules / 760 consumers / 6098 registrations.')

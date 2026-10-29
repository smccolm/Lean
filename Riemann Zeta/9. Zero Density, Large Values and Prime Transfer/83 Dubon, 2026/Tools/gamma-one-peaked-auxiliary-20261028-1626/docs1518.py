from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1518.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1518.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual finite Galois radicals and Kummer injectivity: '+math+' Two exact consumers expand registered scope to 1518 production modules, 885 exact consumers and 6,552 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1518.json').read_text(encoding='utf8'))
section='### Actual finite Galois radicals and Kummer injectivity — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1518.txt').write_text(status+'\n',encoding='utf8');(d/'section1518.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1518
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  SGF --> LCL';assert old in t
new='  SGF --> LCL\n  H90["Proved actual Hilbert-90 radicals with original Galois character ratios"] --> KCI["Proved original character injectivity from actual Kummer power classes"]\n  KCI --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualGaloisKummerCharacterImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1518 production modules, 885 exact consumers and 6552 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualGaloisKummerCharacterPrimaryRecheck20261009']=json.loads((d/'primary-review1518.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Original arithmetic character finiteness and its Galois/Kummer ramification bridge, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='Actual Hilbert 90 now supplies original finite Galois character radicals, and equality of original Kummer classes forces equality of their original character ratios when the base contains the required roots of unity (focused compilation passed; expanded verification pending). Original infinite Galois-character factorization, ramification and root-of-unity descent, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual Hilbert-90 radicals and Kummer character injectivity; 1518 modules / 885 consumers / 6552 registrations.')

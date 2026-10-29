from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1526.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1526.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual Galois class independence and coprime restriction: '+math+' Two exact consumers expand registered scope to 1526 production modules, 893 exact consumers and 6,576 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1526.json').read_text(encoding='utf8'))
section='### Actual Galois class independence and coprime restriction — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1526.txt').write_text(status+'\n',encoding='utf8');(d/'section1526.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1526
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  KCM --> LCL';assert old in t
new='  KCM --> KRI["Proved original Kummer class independent of every actual radical choice"]\n  KRI --> LCL\n  CIR["Proved actual character restriction injective across original coprime quotient"] --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualGaloisClassIndependenceRestrictionImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1526 production modules, 893 exact consumers and 6576 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualGaloisClassIndependenceRestrictionPrimaryRecheck20261009']=json.loads((d/'primary-review1526.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Original arithmetic Galois ramification realization, root-of-unity descent, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='The original Kummer class is now independent of every actual radical realization, and finiteness of original continuous characters descends across a genuine quotient of coprime cardinality (focused compilation passed; expanded verification pending). Original arithmetic Galois ramification realization, the actual root-of-unity extension and its coprime degree, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual Kummer class independence and coprime character restriction; 1526 modules / 893 consumers / 6576 registrations.')

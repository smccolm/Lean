from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1529.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1529.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual cyclotomic Galois character descent: '+math+' Three exact consumers expand registered scope to 1529 production modules, 896 exact consumers and 6,585 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1529.json').read_text(encoding='utf8'))
section='### Actual cyclotomic Galois character descent — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1529.txt').write_text(status+'\n',encoding='utf8');(d/'section1529.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1529
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  CIR["Proved actual character restriction injective across original coprime quotient"] --> LCL';assert old in t
new='  CIR["Proved actual character restriction injective across original coprime quotient"] --> CCD["Proved original continuous prime character descent from actual cyclotomic base"]\n  CPD["Proved actual prime cyclotomic degree divides p minus one"] --> CCD\n  FBT["Proved original Krull topology of finite-base fixing subgroup"] --> CCD\n  CCD --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualCyclotomicGaloisCharacterDescentImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1529 production modules, 896 exact consumers and 6585 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualCyclotomicGaloisCharacterDescentPrimaryRecheck20261009']=json.loads((d/'primary-review1529.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Original arithmetic Galois ramification realization, the actual root-of-unity extension and its coprime degree, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='The actual prime cyclotomic degree now divides p minus one, the finite-base fixing subgroup has its genuine Krull topology, and original continuous prime-character finiteness descends from the actual cyclotomic intermediate field (focused compilation passed; expanded verification pending). Original arithmetic Galois ramification realization, realization of the required cyclotomic intermediate field in that arithmetic extension, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual cyclotomic degree, Krull topology and character descent; 1529 modules / 896 consumers / 6585 registrations.')

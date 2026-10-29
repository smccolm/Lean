from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1530.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1530.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual prime-root unit character embedding: '+math+' One exact consumer expands registered scope to 1530 production modules, 897 exact consumers and 6,590 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1530.json').read_text(encoding='utf8'))
section='### Actual prime-root unit character embedding — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1530.txt').write_text(status+'\n',encoding='utf8');(d/'section1530.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1530
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  CCD --> LCL';assert old in t
new='  CCD --> LCL\n  PRU["Proved actual original prime-order characters embed in genuine field-unit exponent characters"] --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualPrimeRootUnitCharactersImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1530 production modules, 897 exact consumers and 6590 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualPrimeRootUnitCharactersPrimaryRecheck20261009']=json.loads((d/'primary-review1530.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Original arithmetic Galois ramification realization, realization of the required cyclotomic intermediate field in that arithmetic extension, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='Original continuous characters into the group of prime order now embed in actual field-unit-valued exponent characters through the genuine roots of unity (focused compilation passed; expanded verification pending). Original arithmetic Galois ramification realization, realization of the required cyclotomic intermediate field in that arithmetic extension, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual prime-root unit characters; 1530 modules / 897 consumers / 6590 registrations.')

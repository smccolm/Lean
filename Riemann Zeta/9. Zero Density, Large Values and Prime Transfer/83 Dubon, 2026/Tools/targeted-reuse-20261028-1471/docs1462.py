from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1462.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1462.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual ideal-power congruences and original residual matrix p-group: '+math+' Four exact consumers expand registered scope to 1462 production modules, 829 exact consumers and 6,345 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1462.json').read_text(encoding='utf8'))
section='### Actual ideal-power congruences and original residual matrix p-group — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1462.txt').write_text(status+'\n',encoding='utf8');(d/'section1462.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1462
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  CPR --> LCL';assert old in t
new='  CPR --> LCL\n  CGK["Proved literal Artinian residual matrix kernel is a p-group"] --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualResidualMatrixPGroupImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1462 production modules, 829 exact consumers and 6345 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualResidualMatrixPGroupPrimaryRecheck20261009']=json.loads((d/'primary-review1462.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Identification with the original arithmetic Galois group, uniform residual pro-p quotients, arithmetic deformation representability, Galois-specific local conditions, Selmer inputs and patching remain open.'
 assert anchor in t
 extra='The actual Artinian local coefficient residual matrix kernel is now proved a p-group through genuine ideal-power matrix congruences and the original maximal-ideal nilpotence (focused compilation passed; expanded verification pending). Passing to complete coefficient inverse systems, uniform residual pro-p quotients, original arithmetic finiteness and Galois association, deformation representability, Galois-specific local conditions, Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual ideal-power congruences and original residual matrix p-group; 1462 modules / 829 consumers / 6345 registrations.')

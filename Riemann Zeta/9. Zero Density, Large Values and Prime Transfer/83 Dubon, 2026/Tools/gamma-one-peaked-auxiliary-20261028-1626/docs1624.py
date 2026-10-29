from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1624.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1624.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual actual continuous trace-zero coefficient cocycles: '+math+' One exact consumer expands registered scope to 1624 production modules, 991 exact consumers and 6,871 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1624.json').read_text(encoding='utf8'))
section='### Actual actual continuous trace-zero coefficient cocycles — 10 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1624.txt').write_text(status+'\n',encoding='utf8');(d/'section1624.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1624
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  TZAR --> LCL';assert old in t
new='  TZAR --> LCL\n  TZAR --> CTZC["Proved actual continuous trace-zero coefficient cocycles equal original trace-zero matrix cocycles"]\n  CFDC --> CTZC\n  CTZC --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualContinuousTraceZeroCocyclesImplementation20261010']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1624 production modules, 991 exact consumers and 6871 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualContinuousTraceZeroCocyclesPrimaryRecheck20261010']=json.loads((d/'primary-review1624.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Modular Galois association, local deformation conditions at exceptional primes, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='Actual continuous trace-zero coefficient cocycles are linearly equivalent to the original cocycle trace kernel (focused compilation passed; expanded verification pending). Modular Galois association, local deformation conditions at exceptional primes, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual actual continuous trace-zero coefficient cocycles; 1624 modules / 991 consumers / 6871 registrations.')

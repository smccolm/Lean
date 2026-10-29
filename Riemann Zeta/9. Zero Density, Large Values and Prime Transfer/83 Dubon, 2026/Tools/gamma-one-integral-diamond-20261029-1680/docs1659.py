from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1659.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1659.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual original trace-zero arithmetic cotangent dimension and invariants: '+math+' One exact consumer expands registered scope to 1659 production modules, 1026 exact consumers and 7,004 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1659.json').read_text(encoding='utf8'))
section='### Actual original trace-zero arithmetic cotangent dimension and invariants — 10 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1659.txt').write_text(status+'\n',encoding='utf8');(d/'section1659.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1659
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  TZAI --> LCL';assert old in t
new='  TZAI --> LCL\n  AAIC --> ATZID["Proved original trace-zero arithmetic invariant vanishing and genuine local cotangent dimension"]\n  TZAI --> ATZID\n  AUTZ --> ATZID\n  ATZID --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualArithmeticTraceZeroCotangentDimensionImplementation20261010']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1659 production modules, 1026 exact consumers and 7004 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualArithmeticTraceZeroCotangentDimensionPrimaryRecheck20261010']=json.loads((d/'primary-review1659.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Modular Galois association, local deformation conditions at exceptional primes, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='The same original absolutely irreducible arithmetic representation has proved vanishing trace-zero invariants and a genuine completed-ring cotangent dimension formula using its actual trace-zero inertia kernel (focused compilation passed; expanded verification pending). Modular Galois association, local deformation conditions at exceptional primes, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual original trace-zero arithmetic cotangent dimension and invariants; 1659 modules / 1026 consumers / 7004 registrations.')

from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1524.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1524.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Actual unramified radical Selmer membership: '+math+' Three exact consumers expand registered scope to 1524 production modules, 891 exact consumers and 6,569 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1524.json').read_text(encoding='utf8'))
section='### Actual unramified radical Selmer membership — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1524.txt').write_text(status+'\n',encoding='utf8');(d/'section1524.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1524
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  KCM --> LCL';assert old in t
new='  KCM --> LCL\n  UIV["Proved original integral valuation restriction at actual ramification index one"] --> UFV["Proved original fraction-field and unit valuation restriction"]\n  UFV --> URS["Proved original radical Selmer membership from actual unramified primes"]\n  SIR --> URS\n  URS --> LCL'
t=t.replace(old,new,1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['actualUnramifiedRadicalSelmerImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1524 production modules, 891 exact consumers and 6569 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['actualUnramifiedRadicalSelmerPrimaryRecheck20261009']=json.loads((d/'primary-review1524.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Original ramification-to-Selmer valuation conditions, root-of-unity descent, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 assert anchor in t
 extra='Actual ramification index one now preserves original integral, fraction-field and unit valuations, and original radical equations give the genuine Selmer condition outside the actual ramified set (focused compilation passed; expanded verification pending). Original arithmetic Galois ramification realization, root-of-unity descent, arithmetic character finiteness, final framed deformation-functor assembly and fixed residual presentation specialization, Galois association, local conditions, deformation Selmer inputs and patching remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual unramified valuations and original Selmer conditions; 1524 modules / 891 consumers / 6569 registrations.')

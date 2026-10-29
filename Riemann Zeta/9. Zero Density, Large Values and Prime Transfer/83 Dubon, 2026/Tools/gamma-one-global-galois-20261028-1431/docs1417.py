from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026');d=Path('E:/Lean/.tmp/dubon83')
math=(d/'math1417.txt').read_text(encoding='utf8').strip()
remaining=(d/'remaining1417.txt').read_text(encoding='utf8').strip()
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original coordinate fibers and square-zero derivations: '+math+' Four exact consumers expand registered scope to 1417 production modules, 784 exact consumers and 6,189 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1417.json').read_text(encoding='utf8'))
section='### Original coordinate fibers and square-zero derivations — 9 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1417.txt').write_text(status+'\n',encoding='utf8');(d/'section1417.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(s['productionModules'])==1417
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t;pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  FSP --> LCL';assert old in t
new='  FSP --> LCL\n  RCA --> CFD["Proved actual coordinate reduction fibers and square-zero derivation/adjoint-cocycle equivalence"]\n  FOC --> CFD\n  CFD --> LCL'
t=t.replace(old,new,1).replace('OPEN DUB-17: standard unramified induced representation identification and full automorphic Euler interpretation','OPEN DUB-17: higher symmetric automorphic lifts and continuation of the actual Euler functions')
# Remove chronological edges that are not actual proof dependencies.
t=t.replace('  NDL --> FOC[', '  NDL --> LCL\n  FOC[', 1)
t=t.replace('  CFC --> RCA[', '  CFC --> LCL\n  RCA[', 1)
t=t.replace('  RCA --> FSP[', '  ASC --> FSP\n  FHC --> FSP\n  RCA --> FSP[', 1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['coordinateFiberDerivationsImplementation20261009']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1417 production modules, 784 exact consumers and 6189 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
j['coordinateFiberDerivationsPrimaryRecheck20261009']=json.loads((d/'primary-review1417.json').read_text(encoding='utf8'))
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 anchor='Uniform control over all lifts, complete local profinite and pseudodeformation representability, Galois-specific local conditions and Selmer inputs remain open.'
 assert anchor in t
 extra=' Actual coefficient-reduction coordinate fibers now correspond to the original representation fibers. At the original dual-number point, genuine coordinate derivations give exactly the original first-order lifts and adjoint cocycles, with their literal coordinate-value formula (focused compilation passed; expanded verification pending). Uniform finite quotients for all continuous lifts, complete local profinite and pseudodeformation representability, Galois-specific local conditions and Selmer inputs remain open.'
 q.write_text(t.replace(anchor,extra.strip(),1),encoding='utf8')

print('Synchronized actual coordinate fibers and derivations; 1417 modules / 784 consumers / 6189 registrations.')

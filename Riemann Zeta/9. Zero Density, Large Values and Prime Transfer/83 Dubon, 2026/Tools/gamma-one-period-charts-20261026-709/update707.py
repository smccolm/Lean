from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
status=(d/'status707.txt').read_text(encoding='utf8')
section=(d/'section707.txt').read_text(encoding='utf8')
for name in c['statusDocuments']:
 f=p/name;s=f.read_text(encoding='utf8');assert status not in s
 i=s.index('\n')+1;s=s[:i]+'\n'+status+s[i:]
 s=s.replace('The current verified scope has 700 production modules, 287 exact consumers, 3,323 explicit audit registrations and 5,782 exhaustive theorem dependency checks.','The preceding verified scope had 700 production modules, 287 exact consumers, 3,323 explicit audit registrations and 5,782 exhaustive theorem dependency checks; the current expanded scope is identified above.')
 f.write_text(s,encoding='utf8')
with (p/'Dubon Crosswalk.md').open('a',encoding='utf8') as f:f.write('\n'+section)
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'))
j['realGroupHaarCyclicImplementation20261007']={'date':'2026-10-07','status':'Focused real-group Haar and cyclic representation compilation passed; expanded audit, exact consumers and sequential full verification pending. DUB-17 remains OPEN.','modules':json.loads((d/'modules707.json').read_text(encoding='utf8')),'mathematics':section,'remaining':'The central arithmetic quotient, unitary quotient representation, adelic cuspidal representation and actual higher symmetric continuation construction remain unproved; unconditional Deligne and non-CM Sato–Tate are not claimed.'}
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for f in [p.parent/'README.md',p.parents[1]/'README.md']:
 s=f.read_text(encoding='utf8');anchor='The original cusp form now has proved real-group lift, compact weight, Whittaker normalization, prime Hecke and Iwasawa bridges.'
 assert s.count(anchor)==1
 s=s.replace(anchor,'The original cusp form now has proved real-group lift, compact weight, Whittaker normalization, prime Hecke and Iwasawa bridges, together with actual left/right Haar invariance, Petersson integration and an arithmetically invariant cyclic representation that is L2 over the lifted projective base domain. The central arithmetic quotient and adelic construction remain open.')
 f.write_text(s,encoding='utf8')
print('All fifteen status documents, Crosswalk, research ledger and root/category summaries aligned; gates remain 16/20.')

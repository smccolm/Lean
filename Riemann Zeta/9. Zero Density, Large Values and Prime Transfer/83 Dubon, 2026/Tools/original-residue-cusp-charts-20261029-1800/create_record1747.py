from pathlib import Path
import ast,json,re
d=Path('E:/Lean/.tmp/dubon83')
rows=[]
for name in ['unframed','trace-class','original-unframed']:
 rows+=json.loads((d/(name+'-metadata-entries.json')).read_text(encoding='utf8'))
t=(d/'record1737combined.py').read_text(encoding='utf8')
t=t.replace('batches = list(range(1722, 1738))','batches = list(range(1738, 1748))')
t=re.sub(r'^keys = .+$','keys = '+repr(['actual'+r[1]+'Implementation20261010' for r in rows]),t,flags=re.M)
t=t.replace("checks[0][1] == '7251'","checks[0][1] == '7274'")
t=t.replace("'paper1737-console.log'","'paper1747-console.log'")
t=t.replace("len(c['productionModules']) == 1737","len(c['productionModules']) == 1747")
t=t.replace('len(modules) == len(set(modules)) == 16','len(modules) == len(set(modules)) == 10')
t=t.replace('assembled 1737-module','assembled 1747-module')
t=t.replace('The current verified scope has 1721 production modules, 1088 exact consumers, 7,211 explicit audit registrations', 'The current verified scope has 1737 production modules, 1104 exact consumers, 7,251 explicit audit registrations')
t=t.replace("f'The current verified scope has 1737 production modules, 1104 exact consumers, 7,251 explicit audit registrations", "f'The current verified scope has 1747 production modules, 1114 exact consumers, 7,274 explicit audit registrations")
t=t.replace('scope:1737 production modules;1104 exact consumers;7251 explicit registrations','scope:1747 production modules;1114 exact consumers;7274 explicit registrations')
t=t.replace('assembled actual original coefficient-image and retraction increments','assembled actual original unframed trace universal construction')
t=t.replace('assembled scope1737','assembled scope1747')
t=t.replace('### Actual universal trace-ring retraction and complete local data','### Actual original unframed universal trace ring and naturality')
t=t.replace('Sixteen production increments','Ten production increments').replace('scope 1737: 1104 exact consumers, 7,251 explicit registrations','scope 1747: 1114 exact consumers, 7,274 explicit registrations').replace('all sixteen increments','all ten increments')
a=t.index('Choose an original-ring representative');b=t.index('The foundation verifier observed',a)
body='\n\n'.join(r[7] for r in rows)
body+='''

The actual original residual representation supplies every presentation-ring local and topology input. Its true-residue scalar extension carries the original absolute irreducibility hypothesis into the exact original universal representation. The already constructed trace-ring retraction supplies locality, Noetherianity, maximal-adic topology and completeness. One whole continuous trace representation with the exact original residue is then chosen independently of the target. For every complete local target, the genuine existing continuous residue-preserving coefficient fiber maps bijectively to the genuine existing original unframed deformation classes. This same evaluation commutes with the existing coefficient-change and unframed-class maps.

The target category here consists of the actual maximal-adic complete local targets used by the pinned original framed universal property. The theorem retains original absolute residual irreducibility, finite residue field, Noetherian original coefficients and a genuine finitely generated profinite presentation. It does not claim the general pro-Artinian formulation without these restrictions. [de Smit–Lenstra, Theorem2.3 and Propositions2.5/2.6](https://pub.math.leidenuniv.nl/~smitbde/papers/bu-fermat-1995-desmit-lenstra.pdf) supplies the source construction; every proof uses the actual local and pinned Mathlib APIs. No external Lean code was imported.

Exceptional local deformation conditions, full Selmer theory, modular Galois association, patching, higher symmetric automorphy/continuation, unconditional Deligne, non-CM Sato-Tate and the final modular application remain open. DUB-01-16 remain accepted; DUB-17-20 remain OPEN.

'''
t=t[:a]+body+t[b:]
t=t.replace('Tools/actual-coefficient-retraction-route-20261010.json','Tools/actual-original-unframed-route-20261010.json')
t=t.replace('Combined1737 verification recorded','Combined1747 verification recorded')
ast.parse(t)
assert 'c5ea00351c28e24afc9f0f84379aa41082b1188f' in t
assert 'scope 1737:' not in t
(d/'record1747combined.py').write_text(t,encoding='utf8')
print('Combined1747 receipt ready, NOT EXECUTED; ten proposed increments1738-1747 remain uncompiled.')

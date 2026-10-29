from pathlib import Path
import json,re
s=Path(__file__).parent
t=json.loads((s/'anthropic-parabolic-tree-1462'/'sol-tree.json').read_text(encoding='utf-8'))
assert not t.get('truncated',False)
patterns=[r'(GammaOne|Gamma1|GammaH).*(genus|reduc|degree|finrank|integral|smooth)',r'(genus|reduc|degree|finrank|integral|smooth).*(GammaOne|Gamma1|GammaH)',r'(parabolic|H1par|Parabolic).*(coind|induc|surject|dual|pair|lift|transfer)',r'(coind|induc|surject|dual|pair|lift|transfer).*(parabolic|H1par|Parabolic)',r'(H1|Cohomology).*(BinaryForm|binaryForm|specialLinearGroup|Symmetric)',r'(BinaryForm|binaryForm).*(split|retract|section|projectiv)',r'(residue|reduction).*(finrank|genus)']
out={p:[x['path'] for x in t['tree'] if x['path'].endswith('.lean') and re.search(p,x['path'],re.I)] for p in patterns}
f=s/'anthropic-exact-obligation-name-search-1463.json'
with f.open('x',encoding='utf-8') as h:json.dump(out,h,indent=2);h.write('\n')
for p,ns in out.items():
 print(p, len(ns))
 for n in ns:print(' ',n)

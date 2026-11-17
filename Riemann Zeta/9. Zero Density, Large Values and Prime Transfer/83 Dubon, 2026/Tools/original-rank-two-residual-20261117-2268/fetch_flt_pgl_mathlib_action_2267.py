from pathlib import Path
import urllib.request,hashlib,json
p=Path(__file__).parent/'flt-pgl-classification-20261117-2264'
url='https://raw.githubusercontent.com/leanprover-community/mathlib4/1ae49302b2b2d46628179eddf2c7ff0025082c8b/Mathlib/LinearAlgebra/Matrix/Action.lean'
f=p/'Mathlib/LinearAlgebra/Matrix/Action.lean.txt';assert not f.exists();f.parent.mkdir(parents=True,exist_ok=True)
data=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-public-proof-reuse-audit'}),timeout=20).read();f.write_bytes(data)
record=dict(url=url,path=str(f),sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data),purpose='Assess sole missing imported module against pinned Mathlib; no production import or external code execution.')
(p/'mathlib-action-review.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print(json.dumps(record))

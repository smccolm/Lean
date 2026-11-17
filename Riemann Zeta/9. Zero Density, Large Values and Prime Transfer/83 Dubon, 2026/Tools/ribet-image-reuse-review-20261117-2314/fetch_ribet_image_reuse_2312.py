from pathlib import Path
import urllib.request, json, hashlib, datetime, re
s = Path(__file__).parent
dest = s / 'ribet-image-reuse-20261117-2312'
assert not dest.exists()
dest.mkdir()
commit = '6e837e75355538c7f80bab5b956861e86c4eacc2'
tree = json.loads((s / f'flt-ports-487/{commit}-sol-tree.json').read_text())
paths = ['P2M/Sol/' + x['path'] for x in tree['tree'] if 'S_RibetIrr_' in x['path']]
rows = []
imports = set()
def fetch(path):
 url = f'https://raw.githubusercontent.com/anthropics/fermats-last-theorem/{commit}/{path}'
 data = urllib.request.urlopen(urllib.request.Request(url, headers={'User-Agent':'Dubon-proof-reuse-audit'}), timeout=25).read()
 target = dest / (path + '.txt')
 target.parent.mkdir(parents=True, exist_ok=True)
 target.write_bytes(data)
 rows.append(dict(path=str(target.relative_to(dest)), url=url, sha256=hashlib.sha256(data).hexdigest().upper(), bytes=len(data)))
 return data.decode('utf-8')
for path in paths:
 t = fetch(path)
 for n in re.findall(r'(?m)^import (\S+)', t):
  if n.startswith('Definitions.'):
   imports.add(n.replace('.', '/') + '.lean')
for path in sorted(imports):
 fetch(path)
review = dict(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), commit=commit,
 scope='Eight RibetIrr proof candidates and their immediate Definitions imports; source inspection only, not full closure or local build.',
 rootPinsChanged=False, downloadedCodeExecuted=False, files=rows)
(dest / 'review.json').write_text(json.dumps(review, indent=2) + '\n', encoding='utf-8')
print(json.dumps(dict(files=len(rows), bytes=sum(r['bytes'] for r in rows))))

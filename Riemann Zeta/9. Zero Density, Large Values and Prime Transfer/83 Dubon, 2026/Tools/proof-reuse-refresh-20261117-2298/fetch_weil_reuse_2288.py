from pathlib import Path
from datetime import datetime, timezone
import urllib.request, json, hashlib, re

dest = Path(__file__).parent / 'weil-reuse-refresh-20261117-2288'
assert not dest.exists()
dest.mkdir()
rows = []

def fetch(url, path):
    req = urllib.request.Request(url, headers={'User-Agent': 'Dubon-public-proof-reuse-audit'})
    data = urllib.request.urlopen(req, timeout=25).read()
    target = dest / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    rows.append(dict(path=path, url=url, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
    return data

commit = json.loads(fetch('https://api.github.com/repos/AxiomMath/Weil/commits/main', 'commit.json'))['sha']
tree = json.loads(fetch(f'https://api.github.com/repos/AxiomMath/Weil/git/trees/{commit}?recursive=1', 'tree.json'))
assert not tree.get('truncated')
paths = {x['path'] for x in tree['tree'] if x['type'] == 'blob'}
targets = ['README.md', 'LICENSE', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
           'Weil/AlgebraicGeometry/EtaleCohomology/Trace/DeligneWeilConjecture.lean',
           'Weil/AlgebraicGeometry/EtaleCohomology/Trace/WeilRiemannHypothesisForm.lean',
           'Weil/LeanEval/WeilConjectures.lean']
downloaded = {}
for path in targets:
    assert path in paths, path
    downloaded[path] = fetch(f'https://raw.githubusercontent.com/AxiomMath/Weil/{commit}/{path}',
                             path + ('.txt' if path.endswith('.lean') else ''))
imports = set()
for path, data in list(downloaded.items()):
    if path.endswith('.lean'):
        imports.update(re.findall(r'(?m)^(?:public )?import (Weil\.[\w.]+)', data.decode()))
for mod in sorted(imports):
    path = mod.replace('.', '/') + '.lean'
    if path in downloaded:
        continue
    assert path in paths, path
    downloaded[path] = fetch(f'https://raw.githubusercontent.com/AxiomMath/Weil/{commit}/{path}', path + '.txt')
review = dict(recordedUTC=datetime.now(timezone.utc).isoformat(), repository='AxiomMath/Weil',
              commit=commit, leanModules=sum(p.endswith('.lean') for p in paths),
              possibleModularPaths=sorted(p for p in paths if re.search(r'Ramanujan|Petersson|Modular|Cusp|Kuga|Sato|Weight', p, re.I)),
              files=rows, scope='Metadata, three endpoint files, and their immediate Weil imports; not full proof closure.',
              buildClaimed=False, productionMutation=False, rootPinsChanged=False)
(dest / 'review.json').write_text(json.dumps(review, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: review[k] for k in ['commit', 'leanModules', 'possibleModularPaths', 'scope']}))

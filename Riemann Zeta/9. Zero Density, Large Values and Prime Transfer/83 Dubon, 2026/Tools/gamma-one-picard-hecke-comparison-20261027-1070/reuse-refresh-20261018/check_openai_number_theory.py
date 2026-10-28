import hashlib
import json
from pathlib import Path
import urllib.request

out = Path(__file__).parent / 'openai-math'
sha = json.loads((out / 'receipt.json').read_text())['sha']
manifest = []

def fetch(url, name):
    request = urllib.request.Request(url, headers={'User-Agent': 'Dubon-proof-reuse-research'})
    with urllib.request.urlopen(request, timeout=60) as response:
        data = response.read()
    (out / name).write_bytes(data)
    manifest.append({'url': url, 'file': name, 'bytes': len(data),
                     'sha256': hashlib.sha256(data).hexdigest().upper()})
    return data

current = sha
for part in ['lean', 'OAI', 'NumberTheory']:
    tree = json.loads(fetch(f'https://api.github.com/repos/openai/math/git/trees/{current}',
                            f'parent-of-{part}-tree.json'))
    current = next(x['sha'] for x in tree['tree'] if x['path'] == part)
data = fetch(f'https://api.github.com/repos/openai/math/git/trees/{current}?recursive=1',
             'number-theory-tree.json')
tree = json.loads(data)
print('NumberTheory tree:', len(tree['tree']), 'truncated:', tree.get('truncated'))
terms = ['sato', 'automorph', 'modular', 'poitou', 'selmer', 'classfield', 'galois', 'symmetric', 'langlands']
matches = [x['path'] for x in tree['tree'] if any(t in x['path'].lower() for t in terms)]
print('NumberTheory path matches:', json.dumps(matches))
for name in ['CONTENTS.md', 'lean/README.md']:
    fetch(f'https://raw.githubusercontent.com/openai/math/{sha}/{name}', name.replace('/', '__') + '.txt')
(out / 'number-theory-receipt.json').write_text(json.dumps(manifest, indent=2), encoding='utf-8')

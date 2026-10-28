import datetime
import hashlib
import json
from pathlib import Path
import urllib.request

out = Path(__file__).parent / 'openai-math'
out.mkdir(exist_ok=True)

def fetch(url):
    request = urllib.request.Request(url, headers={'User-Agent': 'Dubon-proof-reuse-research'})
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()

head = json.loads(fetch('https://api.github.com/repos/openai/math/commits/HEAD'))
sha = head['sha']
receipt = {'checkedUTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'repository': 'openai/math', 'sha': sha,
           'date': head['commit']['committer']['date'], 'url': head['html_url'],
           'files': []}
for name in ['README.md', 'lean/formalization.yaml', 'lean/lean-toolchain']:
    url = f'https://raw.githubusercontent.com/openai/math/{sha}/{name}'
    try:
        data = fetch(url)
        target = out / (name.replace('/', '__') + '.txt')
        target.write_bytes(data)
        receipt['files'].append({'path': name, 'url': url, 'bytes': len(data),
                                 'sha256': hashlib.sha256(data).hexdigest().upper(),
                                 'file': str(target)})
    except Exception as exc:
        receipt['files'].append({'path': name, 'url': url, 'error': str(exc)})
data = fetch(f'https://api.github.com/repos/openai/math/git/trees/{sha}?recursive=1')
(out / 'tree.json').write_bytes(data)
tree = json.loads(data)
receipt['tree'] = {'truncated': tree.get('truncated'), 'entries': len(tree.get('tree', [])),
                   'sha256': hashlib.sha256(data).hexdigest().upper()}
terms = ['sato', 'automorph', 'modular', 'poitou', 'selmer', 'classfield',
         'class-field', 'galois', 'symmetric-power', 'langlands']
selected = [entry for entry in tree.get('tree', [])
            if any(term in entry['path'].lower() for term in terms)]
(out / 'selected-paths.json').write_text(json.dumps(selected, indent=2), encoding='utf-8')
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2), encoding='utf-8')
print(json.dumps(receipt, indent=2))
print('Selected paths:', len(selected))
for entry in selected:
    if entry['path'].endswith('.lean') or entry['path'].endswith('README.md'):
        print(entry['path'])

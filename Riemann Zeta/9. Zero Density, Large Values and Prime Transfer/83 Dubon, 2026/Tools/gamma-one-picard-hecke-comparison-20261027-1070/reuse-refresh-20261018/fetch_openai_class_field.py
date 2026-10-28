import hashlib
import json
from pathlib import Path
import urllib.request

out = Path(__file__).parent / 'openai-math'
sha = json.loads((out / 'receipt.json').read_text())['sha']
tree = json.loads((out / 'number-theory-tree.json').read_text())
paths = {x['path']: x for x in tree['tree']}
manifest = []
for name in ['Bridge', 'Congruences', 'Kernel', 'Modulus', 'Realization']:
    path = f'DukePrimeDegree/Arithmetic/ClassField{name}.lean'
    url = f'https://raw.githubusercontent.com/openai/math/{sha}/lean/OAI/NumberTheory/{path}'
    request = urllib.request.Request(url, headers={'User-Agent': 'Dubon-proof-reuse-research'})
    with urllib.request.urlopen(request, timeout=60) as response:
        data = response.read()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    if blob != paths[path]['sha']:
        raise RuntimeError(f'Git blob mismatch: {path}')
    target = out / f'ClassField{name}.lean.txt'
    target.write_bytes(data)
    manifest.append({'path': path, 'url': url, 'bytes': len(data),
                     'sha256': hashlib.sha256(data).hexdigest().upper(),
                     'gitBlob': blob, 'gitBlobVerified': True, 'file': str(target)})
(out / 'class-field-manifest.json').write_text(json.dumps(manifest, indent=2), encoding='utf-8')
print(json.dumps([{'path': x['path'], 'bytes': x['bytes']} for x in manifest], indent=2))

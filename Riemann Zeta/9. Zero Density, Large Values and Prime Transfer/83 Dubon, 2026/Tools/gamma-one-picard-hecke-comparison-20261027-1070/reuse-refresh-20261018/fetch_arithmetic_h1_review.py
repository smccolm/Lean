from pathlib import Path
import hashlib, json, urllib.request

base = Path(__file__).parent / 'unramified-h1-review'
commit = '6e837e75355538c7f80bab5b956861e86c4eacc2'
sources = json.loads((base / 'arithmetic-candidates.json').read_text())
assert len(sources) == 3
receipts = []
for source in sources:
    path = source['path']
    assert path.startswith('P2M/Sol/S_') and path.endswith('.lean') and '..' not in path
    url = f'https://raw.githubusercontent.com/anthropics/fermats-last-theorem/{commit}/{path}'
    with urllib.request.urlopen(url, timeout=45) as response:
        body = response.read()
    actual = hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()
    assert actual == source['sha']
    target = base / (Path(path).name + '.txt')
    target.write_bytes(body)
    receipts.append({'url': url, 'path': str(target), 'gitBlob': actual,
        'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest().upper()})
(base / 'arithmetic-source-receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
print(json.dumps(receipts))

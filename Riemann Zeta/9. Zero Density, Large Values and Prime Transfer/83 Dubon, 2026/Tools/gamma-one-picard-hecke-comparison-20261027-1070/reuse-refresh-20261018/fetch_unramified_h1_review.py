from pathlib import Path
import hashlib, json, urllib.request

base = Path(__file__).parent / 'unramified-h1-review'
base.mkdir(exist_ok=True)
commit = '6e837e75355538c7f80bab5b956861e86c4eacc2'
sources = [
    ('S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants.lean',
     'f04f38d40056460b5dc22420ac47ac203a51cf92'),
    ('S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth.lean',
     '7b9609afc980c4956fd12a618545942491f43159'),
]
receipts = []
for name, expected in sources:
    url = f'https://raw.githubusercontent.com/anthropics/fermats-last-theorem/{commit}/P2M/Sol/{name}'
    with urllib.request.urlopen(url, timeout=45) as response:
        body = response.read()
    actual = hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()
    assert actual == expected, name
    target = base / (name + '.txt')
    target.write_bytes(body)
    receipts.append({'url': url, 'path': str(target), 'gitBlob': actual,
        'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest().upper()})
(base / 'source-receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
print(json.dumps(receipts))

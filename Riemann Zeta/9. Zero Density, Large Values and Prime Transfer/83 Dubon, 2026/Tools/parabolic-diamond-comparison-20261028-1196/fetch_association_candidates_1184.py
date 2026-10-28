from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, urllib.request

p = Path(__file__).parent / 'association-reuse-1184'
p.mkdir(exist_ok=False)
rows = []

def fetch(url, name):
    req = urllib.request.Request(url, headers={'User-Agent': 'Dubon-proof-reuse-review'})
    with urllib.request.urlopen(req, timeout=45) as response:
        data = response.read()
    (p / name).write_bytes(data)
    rows.append(dict(url=url, path=name, sha256=hashlib.sha256(data).hexdigest().upper(),
                     bytes=len(data), retrievedUTC=datetime.now(timezone.utc).isoformat()))
    return data

fetch('https://anr-false.github.io/', 'false-home.html.txt')
head = json.loads(fetch('https://api.github.com/repos/mkaratarakis/CICM24_Deligne/commits/main', 'cicm-head.json'))['sha']
for name in ['README.md', 'Statement.lean', 'GaloisReps.lean', 'Frobenius.lean']:
    fetch('https://raw.githubusercontent.com/mkaratarakis/CICM24_Deligne/' + head + '/' + name, name + '.txt')
(p / 'manifest.json').write_text(json.dumps(dict(repository='mkaratarakis/CICM24_Deligne',
    revision=head, files=rows, externalExecution=False), indent=2) + '\n', encoding='utf-8')
print(json.dumps(dict(revision=head, files=len(rows), archive=str(p), externalExecution=False)))

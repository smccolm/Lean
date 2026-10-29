from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, urllib.request

p = Path(__file__).parent
dest = p / 'anthropic-fricke-denominator-depth-1640'
assert not dest.exists()
pin = '6e837e75355538c7f80bab5b956861e86c4eacc2'
name = 'S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem.lean'
url = 'https://raw.githubusercontent.com/anthropics/fermats-last-theorem/' + pin + '/P2M/Sol/' + name
data = urllib.request.urlopen(url, timeout=45).read()
dest.mkdir()
f = dest / (name + '.txt')
f.write_bytes(data)
record = dict(recordedUTC=datetime.now(timezone.utc).isoformat(), pin=pin,
    files=[dict(url=url, path=str(f), bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper())],
    purpose='Read-only source review for the common-denominator obligation in the actual even-weight Fricke trace route serving DUB-17/18.',
    externalBuild=False, externalImport=False)
(dest / 'manifest.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps(record))

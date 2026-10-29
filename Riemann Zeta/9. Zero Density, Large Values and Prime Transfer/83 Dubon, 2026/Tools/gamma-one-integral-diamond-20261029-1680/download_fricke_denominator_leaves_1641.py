from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, urllib.request

p = Path(__file__).parent
dest = p / 'anthropic-fricke-denominator-leaves-1641'
assert not dest.exists()
pin = '6e837e75355538c7f80bab5b956861e86c4eacc2'
names = ['S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean',
         'S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1.lean']
files = []
for name in names:
    url = 'https://raw.githubusercontent.com/anthropics/fermats-last-theorem/' + pin + '/P2M/Sol/' + name
    data = urllib.request.urlopen(url, timeout=45).read()
    files.append((name, url, data))
dest.mkdir()
rows = []
for name, url, data in files:
    f = dest / (name + '.txt')
    f.write_bytes(data)
    rows.append(dict(url=url, path=str(f), bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
record = dict(recordedUTC=datetime.now(timezone.utc).isoformat(), pin=pin, files=rows,
    purpose='Read-only review of coefficient descent and integral spanning needed for the common denominator in the actual Fricke trace route serving DUB-17/18.',
    externalBuild=False, externalImport=False)
(dest / 'manifest.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps(record))

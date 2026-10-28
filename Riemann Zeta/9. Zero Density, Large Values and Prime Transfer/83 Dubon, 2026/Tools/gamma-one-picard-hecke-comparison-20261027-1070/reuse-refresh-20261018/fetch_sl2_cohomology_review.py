from pathlib import Path
import datetime, hashlib, json, urllib.request

p = Path(__file__).parent
idx = json.loads((p.parent / 'anthropic-cft-research-index.json').read_text(encoding='utf-8'))
names = [
    'P2M/Sol/S_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map.lean',
    'P2M/Sol/S_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three.lean',
]
rows = {x['path']: x for x in idx['gitBlobs']}
out = p / 'sl2-cohomology-review'
out.mkdir(exist_ok=True)
receipts = []
for name in names:
    row = rows[name]
    url = f"https://raw.githubusercontent.com/anthropics/fermats-last-theorem/{idx['commit']}/{name}"
    with urllib.request.urlopen(urllib.request.Request(url, headers={'User-Agent': 'Dubon83-reuse-review'}), timeout=30) as response:
        data = response.read()
    assert len(data) == row['size']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['sha']
    f = out / (Path(name).name + '.txt')
    if f.exists():
        assert f.read_bytes() == data
    else:
        f.write_bytes(data)
    receipts.append(dict(row, commit=idx['commit'], url=url, local=str(f),
        sha256=hashlib.sha256(data).hexdigest().upper()))
(out / 'source-receipts.json').write_text(json.dumps({
    'checkedUTC': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'files': receipts,
    'scope': 'Selected source bodies only; not a certified dependency closure.'}, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'files': len(receipts), 'bytes': sum(x['size'] for x in receipts)}))

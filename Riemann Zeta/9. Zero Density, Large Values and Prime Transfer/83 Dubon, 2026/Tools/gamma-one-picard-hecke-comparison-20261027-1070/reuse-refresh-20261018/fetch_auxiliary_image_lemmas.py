from pathlib import Path
import datetime, hashlib, json, urllib.request

p = Path(__file__).parent
index = json.loads((p.parent / 'anthropic-cft-research-index.json').read_text(encoding='utf-8'))
commit = '6e837e75355538c7f80bab5b956861e86c4eacc2'
assert index['commit'] == commit
names = [
 'P2M/Sol/S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible.lean',
 'P2M/Sol/S_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero.lean']
rows = {x['path']: x for x in index['gitBlobs']}
out = p / 'auxiliary-image-review'
out.mkdir(exist_ok=True)
receipt = []
for name in names:
    row = rows[name]
    url = f'https://raw.githubusercontent.com/anthropics/fermats-last-theorem/{commit}/{name}'
    request = urllib.request.Request(url, headers={'User-Agent': 'Dubon83-proof-reuse-review'})
    with urllib.request.urlopen(request, timeout=30) as response:
        data = response.read()
    assert len(data) == row['size']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['sha']
    dest = out / (Path(name).name + '.txt')
    if dest.exists():
        assert dest.read_bytes() == data
    else:
        dest.write_bytes(data)
    receipt.append(dict(row, url=url, file=str(dest), sha256=hashlib.sha256(data).hexdigest().upper()))
record = {'repository': index['repository'], 'commit': commit,
 'checkedUTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'files': receipt, 'scope': 'Two selected source bodies only, not their full dependency closure; no kernel certificate.'}
(out / 'source-receipts.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'files': len(receipt), 'bytes': sum(x['size'] for x in receipt)}))

from pathlib import Path
import datetime, hashlib, json, urllib.request

p = Path(__file__).parent
a = json.loads((p.parent / 'anthropic-cft-research-index.json').read_text(encoding='utf-8'))
t = json.loads((p / 'tau-update-192941/tree.json').read_text(encoding='utf-8'))
jobs = [
    ('anthropics/fermats-last-theorem', a['commit'], a['gitBlobs'], [
        'P2M/Sol/S_groupCohomology_H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range.lean']),
    ('TauCetiProject/TauCeti', '0b4e4720467a7a2bd42af383a284f4246a49aaab', t['tree'], [
        'TauCeti/Algebra/Lie/Sl2/ClebschGordan.lean',
        'TauCeti/Algebra/Lie/Sl2/Standard.lean',
        'TauCeti/Algebra/Lie/Sl2/IntegralLattice.lean'])
]
out = p / 'residual-representation-review'
out.mkdir(exist_ok=True)
receipts = []
for repository, commit, entries, names in jobs:
    rows = {x['path']: x for x in entries}
    for name in names:
        row = rows[name]
        url = f'https://raw.githubusercontent.com/{repository}/{commit}/{name}'
        req = urllib.request.Request(url, headers={'User-Agent': 'Dubon83-proof-reuse-review'})
        with urllib.request.urlopen(req, timeout=30) as response:
            data = response.read()
        assert len(data) == row['size']
        assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['sha']
        dest = out / (repository.split('/')[0] + '-' + Path(name).name + '.txt')
        if dest.exists():
            assert dest.read_bytes() == data
        else:
            dest.write_bytes(data)
        receipts.append(dict(row, repository=repository, commit=commit, url=url,
            file=str(dest), sha256=hashlib.sha256(data).hexdigest().upper()))
record = {'checkedUTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'files': receipts, 'scope': 'Four selected primary source bodies; dependency closures and local kernel status not certified.'}
(out / 'source-receipts.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'files': len(receipts), 'bytes': sum(x['size'] for x in receipts)}))

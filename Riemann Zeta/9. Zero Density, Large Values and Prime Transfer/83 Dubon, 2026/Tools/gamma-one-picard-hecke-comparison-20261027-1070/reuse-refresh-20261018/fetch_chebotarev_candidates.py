from pathlib import Path
import concurrent.futures, hashlib, json, urllib.request

base = Path(__file__).parent
p = base / 'chebotarev-review'
p.mkdir(exist_ok=True)
commit = '0b4e4720467a7a2bd42af383a284f4246a49aaab'
tree = json.loads((base/'tau-update-192941/tree.json').read_text())
blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
names = ['AuxiliaryPrime', 'Density/Chebotarev', 'PrimeCounting/Chebotarev',
         'GaloisCharacter/Nonvanishing', 'Density/Abelian', 'Density/SplittingType']

def fetch(name):
    f = 'TauCeti/NumberTheory/Chebotarev/' + name + '.lean'
    url = f'https://raw.githubusercontent.com/TauCetiProject/TauCeti/{commit}/{f}'
    request = urllib.request.Request(url, headers={'User-Agent': 'Dubon-Lean-proof-reuse-review'})
    with urllib.request.urlopen(request, timeout=35) as response:
        raw = response.read()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest() == blobs[f], f
    out = p/(f+'.txt')
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(raw)
    return {'path': f, 'url': url, 'file': str(out), 'bytes': len(raw),
            'gitBlob': blobs[f], 'sha256': hashlib.sha256(raw).hexdigest().upper()}

with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    files = list(pool.map(fetch, names))
(p/'source-receipts.json').write_text(json.dumps(files, indent=2)+'\n', encoding='utf-8')
print(json.dumps([{'path': x['path'], 'bytes': x['bytes']} for x in files]))

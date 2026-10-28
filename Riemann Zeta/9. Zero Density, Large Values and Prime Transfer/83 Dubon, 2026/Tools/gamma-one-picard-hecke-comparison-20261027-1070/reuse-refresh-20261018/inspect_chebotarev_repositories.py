from pathlib import Path
import concurrent.futures, datetime, hashlib, json, re, urllib.request

base = Path(__file__).parent/'chebotarev-review'
def get(url):
    req=urllib.request.Request(url, headers={'User-Agent':'Dubon-Lean-proof-reuse-review'})
    with urllib.request.urlopen(req, timeout=35) as r:
        return r.read()

def inspect(repo):
    out=base/repo.replace('/','--');out.mkdir(exist_ok=True)
    info=json.loads(get(f'https://api.github.com/repos/{repo}'))
    head=json.loads(get(f'https://api.github.com/repos/{repo}/commits/{info["default_branch"]}'))
    commit=head['sha'];(out/'head.json').write_text(json.dumps(head,indent=2)+'\n')
    raw=get(f'https://api.github.com/repos/{repo}/git/trees/{commit}?recursive=1')
    tree=json.loads(raw);assert not tree.get('truncated');(out/'tree.json').write_bytes(raw)
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    chosen=['lean-toolchain','lakefile.toml','README.md','LICENSE']
    chosen += [f for f in blobs if re.search(r'CebotarevDensity/(Main|Chebotarev|Abelian)\.lean$',f)]
    files=[]
    for f in chosen:
        if f not in blobs:continue
        url=f'https://raw.githubusercontent.com/{repo}/{commit}/{f}';raw=get(url)
        assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[f]
        dest=out/(f+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw)
        files.append({'path':f,'url':url,'sha256':hashlib.sha256(raw).hexdigest().upper(),'bytes':len(raw)})
    receipt={'repository':repo,'commit':commit,'checkedUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'treeComplete':True,'files':files,'kernelCheckedHere':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return {'repository':repo,'commit':commit,'toolchain':(out/'lean-toolchain.txt').read_text().strip(),'files':len(files)}

with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    print(json.dumps(list(pool.map(inspect,['CBirkbeck/aintlib','CBirkbeck/chebotarev-density']))))

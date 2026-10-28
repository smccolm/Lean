from pathlib import Path
import concurrent.futures, hashlib, json, re, urllib.request

base=Path(__file__).parent
localmath=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib')
def fetch_closure(repo, commit, treefile, output, root):
    output.mkdir(exist_ok=True)
    tree=json.loads(treefile.read_text(encoding='utf-8'));assert not tree.get('truncated')
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    modules={f[:-5].replace('/','.') : f for f in blobs if f.endswith('.lean')}
    for f in blobs:
        if f.startswith('projects/') and f.endswith('.lean'):
            modules['.'.join(f[:-5].split('/')[2:])]=f
    queue=[root];seen=set();entries=[];missing=set();newmath=set()
    def fetch(mod):
        f=modules[mod];dest=output/(f+'.txt');dest.parent.mkdir(parents=True,exist_ok=True)
        url=f'https://raw.githubusercontent.com/{repo}/{commit}/{f}'
        raw=dest.read_bytes() if dest.exists() else b''
        blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if blob(raw)!=blobs[f]:
            request=urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-proof-reuse-review'})
            with urllib.request.urlopen(request,timeout=35) as response:raw=response.read()
        assert blob(raw)==blobs[f],f
        dest.write_bytes(raw);s=raw.decode('utf-8')
        imports=re.findall(r'^(?:public )?import (?:all )?([\w.]+)',s,re.M)
        # These are source-review candidates only; comments are removed before scanning.
        code=re.sub(r'/\-.*?\-/','',s,flags=re.S)
        code=re.sub(r'--[^\n]*','',code)
        bad=re.findall(r'^.*(?:\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b|set_option.*(?:maxHeartbeats|maxRecDepth|linter)).*$',code,re.M)
        return {'module':mod,'path':f,'url':url,'gitBlob':blobs[f],
                'sha256':hashlib.sha256(raw).hexdigest().upper(),'bytes':len(raw),
                'imports':imports,'integrityCandidates':bad}
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        while queue:
            batch=sorted(set(queue)-seen);queue=[]
            if not batch:break
            seen.update(batch)
            for entry in pool.map(fetch,batch):
                entries.append(entry)
                for mod in entry['imports']:
                    if mod.startswith('Mathlib'):
                        if not (localmath/(mod.replace('.','/')+'.lean')).exists():newmath.add(mod)
                    elif mod in modules:
                        if mod not in seen:queue.append(mod)
                    elif not mod.startswith(('Lean','Std','Init')):missing.add(mod)
    receipt={'repository':repo,'commit':commit,'endpointModule':root,'files':entries,
             'missingExternalImports':sorted(missing),'mathlibModulesAbsentAtFrozenPin':sorted(newmath),
             'kernelCheckedHere':False,'status':'Pinned source closure reviewed for port feasibility; not a kernel certificate.'}
    (output/'closure-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    return {'repo':repo,'modules':len(entries),'bytes':sum(x['bytes'] for x in entries),
            'integrityCandidates':sum(len(x['integrityCandidates']) for x in entries),
            'absentMathlib':len(newmath),'missingExternal':sorted(missing)}

jobs=[('TauCetiProject/TauCeti','0b4e4720467a7a2bd42af383a284f4246a49aaab',
       base/'tau-update-192941/tree.json',base/'chebotarev-review/tau-density-closure',
       'TauCeti.NumberTheory.Chebotarev.Density.Chebotarev'),
      ('CBirkbeck/aintlib','1e63feb21e2dd9e54908d14c9c07058eff3ff1d4',
       base/'chebotarev-review/CBirkbeck--aintlib/tree.json',base/'chebotarev-review/aintlib-density-closure',
       'CebotarevDensity.Main')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    for r in pool.map(lambda j:fetch_closure(*j),jobs):print(json.dumps(r),flush=True)

from pathlib import Path
import urllib.request,json,hashlib,re
p=Path(__file__).parent
out=p/'patching';out.mkdir(exist_ok=True)
old=p.parent/'reuse-refresh-20261015'/'ImperialCollegeLondon--FLT'
commit='1ab58c167e4fc60bef518cc02caa3fc15c9590d5'
repo='ImperialCollegeLondon/FLT'
def get(url):
    return urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-proof-reuse-review'}),timeout=45).read()
raw=get(f'https://api.github.com/repos/{repo}/git/trees/{commit}?recursive=1')
tree=json.loads(raw);assert not tree.get('truncated')
(out/'tree.json').write_bytes(raw)
blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
queue=['FLT/Patching/REqualsT.lean'];seen=set();entries=[]
while queue:
    f=queue.pop(0)
    if f in seen:continue
    seen.add(f)
    prev=old/(f+'.txt')
    content=prev.read_bytes() if prev.exists() else b''
    blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    reused=bool(content) and blob(content)==blobs[f]
    url=f'https://raw.githubusercontent.com/{repo}/{commit}/{f}'
    if not reused:content=get(url)
    assert blob(content)==blobs[f],f
    dest=out/(f+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(content)
    text=content.decode('utf-8')
    imports=re.findall(r'^(?:public )?import ([\w.]+)',text,re.M)
    queue += [x.replace('.','/')+'.lean' for x in imports if x.startswith('FLT.')]
    code=re.sub(r'/\-.*?\-/','',text,flags=re.S)
    violations=re.findall(r'^.*(?:\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b|set_option.*(?:maxHeartbeats|maxRecDepth|linter)).*$',code,re.M)
    entries.append({'path':f,'url':url,'gitBlob':blobs[f],'sha256':hashlib.sha256(content).hexdigest().upper(),
      'bytes':len(content),'imports':imports,'sameAsOctober15':reused,'integrityCandidates':violations})
for f in ['LICENSE','lean-toolchain']:
    content=get(f'https://raw.githubusercontent.com/{repo}/{commit}/{f}')
    assert hashlib.sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest()==blobs[f]
    (out/(f+'.txt')).write_bytes(content)
receipt={'repository':repo,'commit':commit,'endpoint':'ker_RtoT_le_nilradical','files':entries,
 'treeComplete':True,'kernelCheckedHere':False,
 'purpose':'DUB-17 higher symmetric-power continuation <- arithmetic automorphy lifting <- patching with actual deformation rings and Hecke modules. Assess this generic proved closure for porting at the unchanged Dubon pin; arithmetic system realization remains separate.'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'files':len(entries),'sameAsOctober15':sum(x['sameAsOctober15'] for x in entries),
 'integrityCandidates':sum(len(x['integrityCandidates']) for x in entries),'kernelCheckedHere':False}))

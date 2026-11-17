from pathlib import Path, PurePosixPath
import urllib.request,json,hashlib,datetime,re
p=Path(__file__).parent;dest=p/'padic-modular-review-2517';assert not dest.exists()
headers={'User-Agent':'Dubon83-proof-reuse-review','Accept':'application/vnd.github+json'}
def get(url):
 with urllib.request.urlopen(urllib.request.Request(url,headers=headers),timeout=30) as r:return r.read()
base='https://api.github.com/repos/ANR-FALSE/PadicModForms'
head=json.loads(get(base+'/commits/master'));sha=head['sha']
assert re.fullmatch(r'[0-9a-f]{40}',sha)
tree=json.loads(get(base+'/git/trees/'+sha+'?recursive=1'));assert not tree.get('truncated')
files=[x['path'] for x in tree['tree'] if x['type']=='blob' and (x['path'].endswith('.lean') or x['path'] in ['README.md','LICENSE','lean-toolchain','lake-manifest.json','lakefile.toml'])]
assert len(files)<250
for name in files:
 q=PurePosixPath(name);assert not q.is_absolute() and '..' not in q.parts
pending=[];size=0
for name in files:
 url='https://raw.githubusercontent.com/ANR-FALSE/PadicModForms/'+sha+'/'+name
 data=get(url);size+=len(data);assert size<20000000
 pending.append((name,url,data))
dest.mkdir();rows=[]
for name,url,data in pending:
 target=dest/(name+('.txt' if name.endswith('.lean') else ''));target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 rows.append(dict(source=name,path=str(target),url=url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(dest/'head.json').write_text(json.dumps(head,indent=2)+'\n')
(dest/'tree.json').write_text(json.dumps(tree,indent=2)+'\n')
manifest=dict(retrievedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),repository='https://github.com/ANR-FALSE/PadicModForms',commit=sha,commitUTC=head['commit']['committer']['date'],sourceFiles=len(files),bytes=size,files=rows,status='Read-only source inspection; no external code executed or imported into production; no proof closure accepted.')
(dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in manifest.items() if k!='files'}))

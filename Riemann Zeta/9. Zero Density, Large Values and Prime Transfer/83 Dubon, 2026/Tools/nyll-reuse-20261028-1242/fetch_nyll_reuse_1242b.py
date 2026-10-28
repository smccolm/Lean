from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
import json,hashlib
p=Path(__file__).parent/'nyll-reuse-1242b'
p.mkdir(exist_ok=False)
base='https://api.github.com/repos/n-yamaguchi-0729/NYLL'
records=[]
def fetch(url,name):
 data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review','Accept':'application/vnd.github+json'}),timeout=40).read()
 f=p/name;f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists();f.write_bytes(data)
 records.append(dict(url=url,path=name,sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data)))
 return data
commit=json.loads(fetch(base+'/commits/main','commit.json'));rev=commit['sha']
tree=json.loads(fetch(base+'/git/trees/'+rev+'?recursive=1','tree.json'))
assert not tree.get('truncated',False)
for name in ['README.md','lean-toolchain','lake-manifest.json','NOTICE','LICENSE']:
 fetch('https://raw.githubusercontent.com/n-yamaguchi-0729/NYLL/'+rev+'/'+name,name+'.txt')
matches=[x['path'] for x in tree['tree'] if x['type']=='blob' and any(k.lower() in x['path'].lower() for k in ['Frobenius','GoodReduction','SmoothProper','TraceFormula','Jacobian','Parabolic','ModularForm'])]
(p/'candidates.json').write_text(json.dumps(matches,indent=2)+'\n',encoding='utf-8')
(p/'fetch-manifest.json').write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository='n-yamaguchi-0729/NYLL',revision=rev,commitDate=commit['commit']['committer']['date'],files=records,externalBuild=False,externalImport=False,productionMutation=False),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(revision=rev,commitDate=commit['commit']['committer']['date'],treeFiles=len(tree['tree']),candidatePaths=len(matches),toolchain=(p/'lean-toolchain.txt').read_text().strip())))

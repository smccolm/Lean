from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
import json,hashlib,re
s=Path(__file__).parent
out=s/'anthropic-parabolic-tree-1462';out.mkdir(exist_ok=False)
repo='anthropics/fermats-last-theorem'
rows=[]
def fetch(url,name):
 data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review','Accept':'application/vnd.github+json'}),timeout=45).read()
 f=out/name
 with f.open('xb') as h:h.write(data)
 rows.append(dict(url=url,path=str(f),sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data)))
 return json.loads(data)
api='https://api.github.com/repos/'+repo
head=fetch(api+'/commits/HEAD','head.json');rev=head['sha']
root=fetch(api+'/git/trees/'+rev,'root-tree.json');assert not root.get('truncated',False)
entry=next(x for x in root['tree'] if x['path']=='P2M' and x['type']=='tree')
p2m=fetch(api+'/git/trees/'+entry['sha'],'p2m-tree.json');assert not p2m.get('truncated',False)
entry=next(x for x in p2m['tree'] if x['path']=='Sol' and x['type']=='tree')
sol=fetch(api+'/git/trees/'+entry['sha']+'?recursive=1','sol-tree.json')
paths=['P2M/Sol/'+x['path'] for x in sol['tree'] if x['type']=='blob' and x['path'].endswith('.lean')]
patterns=[r'parabolic.*(surject|transfer|coind|shapiro|restrict|lifting|lift)',r'(surject|transfer|coind|shapiro|restrict|lifting|lift).*parabolic',r'(SL2|SpecialLinear|specialLinear).*(H1|[Cc]ohom|[Cc]ocycle)',r'(H1|[Cc]ohom|[Cc]ocycle).*(SL2|SpecialLinear|specialLinear)',r'parabolic.*(dual|pairing|perfect)',r'(dual|pairing|perfect).*parabolic']
chosen={pat:[p for p in paths if re.search(pat,p,re.I)] for pat in patterns}
manifest=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository=repo,revision=rev,commitDate=head['commit']['committer']['date'],previousInspectedRevision='6e837e75355538c7f80bab5b956861e86c4eacc2',headChanged=rev!='6e837e75355538c7f80bab5b956861e86c4eacc2',treeComplete=not sol.get('truncated',False),leanFiles=len(paths),candidates=chosen,files=rows,scope='Filename discovery in the pinned P2M/Sol subtree only; no absence inference if truncated, and filenames are not proof verification.',externalBuild=False,externalImport=False,productionMutation=False)
(out/'review-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:manifest[k] for k in ['revision','commitDate','headChanged','treeComplete','leanFiles','candidates']},indent=2))

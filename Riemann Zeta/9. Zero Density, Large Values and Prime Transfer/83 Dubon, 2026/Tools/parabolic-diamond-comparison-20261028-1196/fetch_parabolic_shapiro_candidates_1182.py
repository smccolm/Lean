from pathlib import Path
from datetime import datetime,timezone
import json,urllib.request,hashlib,concurrent.futures
p=Path(__file__).parent/'parabolic-shapiro-reuse-1182'
p.mkdir(exist_ok=False)
jobs=[('prove2-shapiro.html.txt','https://beta.prove2.me/theorems/96bbed5a-210d-4d60-8934-d83a912e2875'),('prove2-shapiro-main.html.txt','https://prove2.me/theorems/96bbed5a-210d-4d60-8934-d83a912e2875'),('wiese-parabolic-faithfulness.html.txt','https://arxiv.org/html/math/0511115v3')]
def fetch(job):
 name,url=job
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research'}),timeout=35) as res:
   b=res.read();final=res.url
  f=p/name;f.write_bytes(b)
  return dict(path=str(f),url=url,finalURL=final,sha256=hashlib.sha256(b).hexdigest().upper(),retrievedUTC=datetime.now(timezone.utc).isoformat())
 except Exception as e:return dict(url=url,error=str(e),retrievedUTC=datetime.now(timezone.utc).isoformat())
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(fetch,jobs))
(p/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')
print(json.dumps(rows))

from pathlib import Path
from datetime import datetime,timezone
from concurrent.futures import ThreadPoolExecutor
import urllib.request,json,re,hashlib,time
p=Path(__file__).parent
root=p/'flt-pgl-classification-20261117-2264'
assert not root.exists()
root.mkdir()
commit='478c1013cd29c27d72f57aa8b691fa46083664b3'
base='https://raw.githubusercontent.com/ImperialCollegeLondon/FLT/'+commit+'/'
rows=[];errors=[]
def fetch(path):
 url=base+path
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Dubon-public-proof-reuse-audit'})
  data=urllib.request.urlopen(req,timeout=20).read()
  target=root/(path+('.txt' if path.endswith('.lean') else ''))
  target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
  return dict(path=path,url=url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()),data.decode('utf-8')
 except Exception as e:return dict(path=path,url=url,error=str(e)),None
for path in ['LICENSE','lean-toolchain','lakefile.toml','lake-manifest.json']:
 row,t=fetch(path)
 (rows if t is not None else errors).append(row)
seen=set();frontier={'FLT.KnownIn1980s.PGL2.Proofs'};imports={};mathlib=set()
with ThreadPoolExecutor(max_workers=5) as pool:
 while frontier:
  assert len(seen)+len(frontier)<=500,'Bounded source review exceeded 500 modules'
  batch=sorted(frontier);frontier=set();seen.update(batch)
  for module,(row,t) in zip(batch,pool.map(lambda m:fetch(m.replace('.','/')+'.lean'),batch)):
   if t is None: errors.append(row);continue
   rows.append(row)
   code=re.sub(r'/\-.*?\-/','',t,flags=re.S);code=re.sub(r'--[^\n]*','',code)
   deps=[]
   for line in re.findall(r'^\s*(?:public\s+)?import\s+(.+)$',code,re.M):deps.extend(re.findall(r'[A-Z][A-Za-z0-9_.]*',line))
   imports[module]=deps
   row['prohibitedSyntax']=sorted(set(re.findall(r'\b(?:sorry|admit|axiom|constant|unsafe|native_decide|implemented_by)\b',code)))
   row['limitOrLinterOptions']=re.findall(r'^\s*(?:set_option|attribute\s+\[-?)[^\n]+',code,re.M)
   frontier.update(d for d in deps if d.startswith('FLT.') and d not in seen)
   mathlib.update(d for d in deps if d.startswith('Mathlib.'))
record=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository='ImperialCollegeLondon/FLT',commit=commit,sourceOfCommit='Official generated documentation source link; not a claim about current remote HEAD.',entry='FLT.KnownIn1980s.PGL2.Proofs',files=rows,errors=errors,imports=imports,mathlibImports=sorted(mathlib),fetchedModuleCount=len(imports),unbuilt=True,productionMutation=False,limits='No external proof build or axiom audit is claimed. Import closure syntax review is research evidence only; production acceptance requires source-object bridges and the pinned local kernel audit.')
f=root/'review.json';f.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(record=str(f),modules=len(imports),files=len(rows),errors=errors,flagged=[r['path'] for r in rows if r.get('prohibitedSyntax')],sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper())))

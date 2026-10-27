from pathlib import Path
import json,urllib.request,hashlib,difflib
p=Path(r"E:\Lean\.tmp\dubon83\reuse-head-refresh-741")
heads={r['repository']:r['head'] for r in json.loads((p/'manifest.json').read_text())['repositories']}
rows=[]
def fetch(repo,path,blob=None,name=None,rev=None):
 url='https://raw.githubusercontent.com/'+repo+'/'+(rev or heads[repo])+'/'+path
 f=p/(name or repo.replace('/','__')+'__'+path.replace('/','__')+'.txt');assert not f.exists()
 b=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research'}),timeout=60).read();f.write_bytes(b)
 git=hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()
 if blob:assert git==blob
 rows.append(dict(path=str(f),source=path,url=url,sha256=hashlib.sha256(b).hexdigest().upper(),gitBlob=git,blobVerified=bool(blob),bytes=len(b)))
 print(json.dumps(rows[-1]),flush=True);return b
for name,sha in [('ArithmeticGeometry','87d83a4ec3679189dfdc8b5bbd8e7e5faa89692a'),('RepresentationTheory','5782a864385557f904f8674a9ea89e8cd9fe89d0')]:
 url='https://api.github.com/repos/openai/math/git/trees/'+sha+'?recursive=1';f=p/('openai__math-'+name+'-tree.json');assert not f.exists()
 b=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research'}),timeout=60).read();f.write_bytes(b);v=json.loads(b)
 rows.append(dict(path=str(f),url=url,sha256=hashlib.sha256(b).hexdigest().upper(),entries=len(v['tree']),truncated=v.get('truncated')));print(json.dumps(rows[-1]),flush=True)
t={x['path']:x for x in json.loads((p/'openai__math-AlgebraicGeometry-tree.json').read_text())['tree']}
for name in ['ClosedImmersion/HolomorphicCharts.lean','ClosedImmersion/NormalCoordinates.lean','ComplexPoint/AnalyticMap.lean','Seshadri/Analytic/ConvergentSeries.lean']:
 fetch('openai/math','lean/OAI/AlgebraicGeometry/'+name,t[name]['sha'])
for name in ['lean/README.md','lean/lean-toolchain','lean/lake-manifest.json','lean/formalization.yaml','LICENSE']:
 fetch('openai/math',name)
c=json.loads((p/'leanprover-community__mathlib4-compare.json').read_text());base=c['base_commit']['sha']
t={x['path']:x for x in json.loads((p/'leanprover-community__mathlib4-tree.json').read_text())['tree']}
for name in ['Discriminant','LevelOne/DimensionFormula','QExpansion','RamanujanFormula']:
 path='Mathlib/NumberTheory/ModularForms/'+name+'.lean'
 b=fetch('leanprover-community/mathlib4',path,t[path]['sha'])
 old=fetch('leanprover-community/mathlib4',path,name='mathlib-previous-'+name.replace('/','__')+'.lean.txt',rev=base)
 diff=''.join(difflib.unified_diff(old.decode().splitlines(True),b.decode().splitlines(True),fromfile=base,tofile=heads['leanprover-community/mathlib4']))
 with (p/('mathlib-'+name.replace('/','__')+'.diff.txt')).open('x',encoding='utf-8') as f:f.write(diff)
with (p/'additional-primary-snapshots.json').open('x',encoding='utf-8') as f:json.dump(rows,f,indent=2);f.write('\n')

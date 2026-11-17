from pathlib import Path
import json,re,hashlib
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
evidence=[]
def read(name,count):
 f=s/(name+'.log');assert f.with_suffix('.exit').read_text().strip()=='0'
 t=f.read_text('utf-16')
 assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',t)
 rows=re.findall(r'^SEMANTIC (\S+) (\S+): (\d+) (\d+|NONE)$',t,re.M)
 assert len(rows)==len({n for _,n,_,_ in rows})==count
 for p in [f,f.with_suffix('.lean'),f.with_suffix('.exit')]:evidence.append(dict(path=str(p),sha256=sha(p)))
 return {n:dict(owner=m,typeHash=ty,valueHash=value) for m,n,ty,value in rows}
scratch={}; production={}
for left,right,count in [('SourceOriginalSymmetricScratchSemantic2360', 'SourceOriginalSymmetricProductionSemantic2360', 95), ('SourceOriginalSymmetricAdjointScratchSemantic2375', 'SourceOriginalSymmetricAdjointProductionSemantic2375', 17), ('SourceOriginalTwistedKernelScratchSemantic2379', 'SourceOriginalTwistedKernelProductionSemantic2379', 48), ('SourceOriginalSymmetricJointScratchSemantic2385', 'SourceOriginalSymmetricJointProductionSemantic2385', 18)]:
 a=read(left,count);b=read(right,count)
 assert not set(a)&set(scratch) and not set(b)&set(production)
 scratch.update(a);production.update(b)
assert len(scratch)==len(production)==178
missing=sorted(set(scratch)-set(production));extra=sorted(set(production)-set(scratch))
different={n:dict(scratch=scratch[n],production=production[n]) for n in scratch.keys()&production.keys() if scratch[n]!=production[n]}
ok=not missing and not extra and not different
result=dict(passed=ok,declarations=178,missing=missing,extra=extra,different=different,evidence=evidence,
 normalization='Names are rewritten structurally, retaining numerical Name components: only the exact import-qualified private prefixes, generated auxiliary macro/unexpander names and three verified prime-instance names change. Bound binder names are alpha-normalized, expression metadata is removed after recursive child traversal, and closed Name literals are normalized only in generated notation declarations. Every public/private/generated type and available value is checked with exact owner/name sets; no declaration is omitted. Identical mathematical source bodies are independently checked after stripping imports.')
out=s/('source-original-symmetric-semantic-comparison-9755.json' if ok else 'source-original-symmetric-semantic-diagnostic-9755d.json')
assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(passed=ok,declarations=178,missing=len(missing),extra=len(extra),different=len(different),record=out.name)))
assert ok,'Type/value mismatch retained for inspection; no canonical receipt is authorized.'

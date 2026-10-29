from pathlib import Path
import json
s=Path(__file__).parent
old=s/'SourceSiegelProductCore1565a.lean'
t=old.read_text(encoding='utf-8')
a='unfold siegelFun pref sprod qq qa; simp only [mul_assoc]'
b='rw [siegelFun_def]; unfold pref sprod qq qa; simp only [mul_assoc]'
assert t.count(a)==1;t=t.replace(a,b)
assert not old.with_suffix('.lean.txt').exists();old.rename(old.with_suffix('.lean.txt'))
f=s/'SourceSiegelProductCore1565b.lean';assert not f.exists();f.write_text(t,encoding='utf-8')
v=json.loads((s/'siegel-function-versions-1577.json').read_text(encoding='utf-8'));v['SourceSiegelProductCore']='1565b'
f=s/'siegel-function-versions-1579.json';assert not f.exists();f.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
review=dict(reason='The initial 19-module preflight passed exhaustive axioms and all 16 linters per module. The value dependency check found exactly one missing public entry: siegelFun_def. The actual product factorization now rewrites with this literal-definition theorem instead of unfolding the definition directly. This is the same mathematical equality and proof route; it establishes the advertised source entry in the actual endpoint proof term, without adding a premise or detached check. Earlier evidence remains intact.',versionChange={'SourceSiegelProductCore':['1565a','1565b']},downstreamBodiesUnchanged=True)
f=s/'siegel-source-entry-review-1579.json';assert not f.exists();f.write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')

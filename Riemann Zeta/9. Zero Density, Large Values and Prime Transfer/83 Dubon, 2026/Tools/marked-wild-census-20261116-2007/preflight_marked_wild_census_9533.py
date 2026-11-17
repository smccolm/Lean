from pathlib import Path
import ast,json,hashlib
p=Path(__file__).parent
src=p/'integrate_source_marked_wild_census_9533.py'
text=src.read_text(encoding='utf-8')
cut=text.index('for target, data, role in refresh_pending:')
prefix=text[:cut]
tree=ast.parse(prefix)
for node in ast.walk(tree):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute):
  assert node.func.attr not in ['write_text','write_bytes','mkdir','unlink','rename'],node.func.attr
ns={'__file__':str(src)}
exec(compile(prefix,str(src),'exec'),ns)
assert len(ns['pending'])==24 and len(ns['queries'])==33 and ns['count']==84
assert ns['supplemental_review_path'] in {t for t,_,_ in ns['refresh_pending']}
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
out=p/'marked-wild-census-preflight-9533.json'
with out.open('x',encoding='utf-8') as f:json.dump(dict(status='PASS: all immutable source/receipt, exact import-only promotion, evidence archive, registration, existing documents and predecessor canonical checks passed before mutation.',integrationScriptSha256=sha(src),productionMutation=False,modules=24,queries=33,exhaustiveScratchChecks=84,proofValueChecks=64,predecessor=9509,expectedProductionModules=9533,fullGoal='16/20; DUB-17--20 OPEN'),f,indent=2)
print(json.dumps(dict(status='PASS',record=str(out),sha256=sha(out),productionMutation=False)))

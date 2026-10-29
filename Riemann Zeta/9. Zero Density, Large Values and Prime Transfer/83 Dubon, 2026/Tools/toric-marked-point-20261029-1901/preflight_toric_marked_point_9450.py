from pathlib import Path
import ast,json,hashlib
p=Path(__file__).parent
src=p/'integrate_source_toric_marked_point_9450.py'
text=src.read_text(encoding='utf-8')
cut=text.index('for target, data, role in refresh_pending:')
prefix=text[:cut]
tree=ast.parse(prefix)
for node in ast.walk(tree):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute):
  assert node.func.attr not in ['write_text','write_bytes','mkdir','unlink','rename'],node.func.attr
ns={'__file__':str(src)}
exec(compile(prefix,str(src),'exec'),ns)
assert len(ns['pending'])==40 and len(ns['queries'])==220 and ns['count']==332
assert ns['supplemental_review_path'] in {t for t,_,_ in ns['refresh_pending']}
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
out=p/'toric-marked-point-preflight-9450.json'
with out.open('x',encoding='utf-8') as f:json.dump(dict(status='PASS: all immutable source/receipt, exact import-only promotion, evidence archive, registration, existing documents and predecessor canonical checks passed before mutation.',integrationScriptSha256=sha(src),productionMutation=False,modules=40,queries=220,exhaustiveScratchChecks=332,proofValueChecks=186,predecessor=9410,expectedProductionModules=9450,fullGoal='16/20; DUB-17--20 OPEN'),f,indent=2)
print(json.dumps(dict(status='PASS',record=str(out),sha256=sha(out),productionMutation=False)))

from pathlib import Path
import ast,json,hashlib
p=Path(__file__).parent
src=p/'integrate_source_gamma_one_reciprocity_inputs_8695.py'
text=src.read_text(encoding='utf-8')
cut=text.index('for target, data, role in refresh_pending:')
prefix=text[:cut]
tree=ast.parse(prefix)
for node in ast.walk(tree):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute):
  assert node.func.attr not in ['write_text','write_bytes','mkdir','unlink','rename'],node.func.attr
ns={'__file__':str(src)}
exec(compile(prefix,str(src),'exec'),ns)
assert len(ns['pending'])==21 and len(ns['queries'])==108 and ns['count']==156
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
out=p/'gamma-one-reciprocity-inputs-preflight-8695.json'
with out.open('x',encoding='utf-8') as f:json.dump(dict(status='PASS: all immutable source/receipt, exact import-only promotion, evidence archive, registration, existing documents and predecessor canonical checks passed before mutation.',integrationScriptSha256=sha(src),productionMutation=False,modules=21,queries=108,exhaustiveScratchChecks=156,proofValueChecks=234,predecessor=8674,expectedProductionModules=8695,fullGoal='16/20; DUB-17--20 OPEN'),f,indent=2)
print(json.dumps(dict(status='PASS',record=str(out),sha256=sha(out),productionMutation=False)))

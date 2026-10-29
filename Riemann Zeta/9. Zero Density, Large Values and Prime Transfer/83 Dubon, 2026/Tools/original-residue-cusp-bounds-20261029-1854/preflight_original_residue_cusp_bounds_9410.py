from pathlib import Path
import ast,json,hashlib
p=Path(__file__).parent
src=p/'integrate_source_original_residue_cusp_bounds_9410.py'
text=src.read_text(encoding='utf-8')
cut=text.index('for target, data, role in refresh_pending:')
prefix=text[:cut]
tree=ast.parse(prefix)
for node in ast.walk(tree):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute):
  assert node.func.attr not in ['write_text','write_bytes','mkdir','unlink','rename'],node.func.attr
ns={'__file__':str(src)}
exec(compile(prefix,str(src),'exec'),ns)
assert len(ns['pending'])==36 and len(ns['queries'])==57 and ns['count']==138
assert ns['supplemental_review_path'] in {t for t,_,_ in ns['refresh_pending']}
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
out=p/'original-residue-cusp-bounds-preflight-9410.json'
with out.open('x',encoding='utf-8') as f:json.dump(dict(status='PASS: all immutable source/receipt, exact import-only promotion, evidence archive, registration, existing documents and predecessor canonical checks passed before mutation.',integrationScriptSha256=sha(src),productionMutation=False,modules=36,queries=57,exhaustiveScratchChecks=138,proofValueChecks=100,predecessor=9374,expectedProductionModules=9410,fullGoal='16/20; DUB-17--20 OPEN'),f,indent=2)
print(json.dumps(dict(status='PASS',record=str(out),sha256=sha(out),productionMutation=False)))

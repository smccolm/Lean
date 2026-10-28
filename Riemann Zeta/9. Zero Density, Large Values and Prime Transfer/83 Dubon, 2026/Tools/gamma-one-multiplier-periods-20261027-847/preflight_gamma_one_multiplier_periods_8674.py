from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).parent;r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
meta=json.loads((p/'gamma-one-multiplier-periods-preexecution-review-8674.json').read_text(encoding='utf-8'))
assert (meta['modules'],meta['queries'],meta['theorems'],meta['constructions'],meta['exhaustiveScratchChecks'],meta['proofValueChecks'])==(42,273,207,66,352,350)
for row in meta['scripts']:
 f=Path(row['path']);assert sha(f)==row['sha256'],f
 if f.suffix=='.py':ast.parse(f.read_text(encoding='utf-8'))
cfg=json.loads((r/'Tools/scaffold.json').read_text(encoding='utf-8'))
assert len(cfg['productionModules'])==8632
mods=[];qs=[];rows=[]
for n,digest in meta['receipts'].items():
 f=p/n;assert sha(f)==digest
 c=json.loads(f.read_text(encoding='utf-8'));mods+=c['modules'];qs+=c['queries']
 assert c['exit']==c['diagnostics']==0
 for field,hashfield in [('log','logSha256'),('dependencyAuditLog','dependencyAuditSha256'),('reuseReview','reuseReviewSha256')]:
  assert sha(Path(c[field]))==c[hashfield]
 for row in c['files']:
  f=Path(row['path']);assert sha(f)==row['sha256'] and sha(f.with_suffix('.olean'))==row['oleanSha256']
  assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
  assert not (r/'Extension/Dubon2026'/f.name).exists()
  rows.append(dict(module=f.stem,sha256=sha(f)))
assert len(mods)==len(set(mods))==42 and len(qs)==len(set(qs))==273
a=(r/'Extension/Dubon2026/Audit.lean').read_text(encoding='utf-8')
for q in qs:assert not re.search(chr(96)*2+re.escape(q)+r'(?=[,\s])',a),q
known=set(cfg['productionModules'])|set(mods)
for m in mods:
 s=(p/(m+'.lean')).read_text(encoding='utf-8')
 for imp in re.findall(r'^import (\S+)',s,re.M):
  assert imp=='Mathlib' or imp.startswith(('Mathlib.','Dubon2026.')) or imp in known,(m,imp)
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|nolint|trace_state',code)
t=(p/'integrate_source_gamma_one_multiplier_periods_8674.py').read_text(encoding='utf-8')
tree=ast.parse(t);assign={n.targets[0].id:n.value for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)}
edge=ast.literal_eval(assign['edge']);assert (r/'Dubon Architecture.md').read_text(encoding='utf-8').count(edge)==1
assert 'canonical-evidence-8632.json' in t and 'receipt8632' in t
for rel in cfg['statusDocuments']+['Dubon Remaining Obligations.md']:assert '\n\n' in (r/rel).read_text(encoding='utf-8')
out=p/'gamma-one-multiplier-periods-preflight-8674.json'
with out.open('x',encoding='utf-8') as f:json.dump(dict(status='Static preflight PASS; preceding canonical receipt and archive remain enforced at integration time.',sourceFiles=rows,modules=42,queries=273,exhaustiveScratchTheorems=352,requiredDependencyChecks=350,scripts=meta['scripts'],productionMutation=False,fullGoal='16/20; DUB-17--20 OPEN.'),f,indent=2);f.write('\n')
print(json.dumps(dict(status='PASS',modules=42,queries=273,productionMutation=False,receipt=str(out))))

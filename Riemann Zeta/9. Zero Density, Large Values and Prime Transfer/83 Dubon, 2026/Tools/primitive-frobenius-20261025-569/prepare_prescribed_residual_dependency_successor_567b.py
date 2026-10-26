from pathlib import Path
import json,hashlib
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old='Dubon2026.SourceFunctionField.original_tate_free_finite_rank'
new='Dubon2026.SourceFunctionField.OriginalChart.original_tate_free_finite_rank'
a=p/'SourceOriginalPrescribedResidualFrobeniusDependencyAudit2.lean'
log=a.with_suffix('.log')
assert a.with_suffix('.exit').read_text().strip()=='1'
assert log.read_text(encoding='utf-16').strip().endswith('Missing original source proof dependencies: ['+old+']')
c=p/'source-original-prescribed-residual-frobenius-2-audit-config.json'
cfg=json.loads(c.read_text(encoding='utf-8'))
assert cfg['proofEdges'].count(old)==1 and new not in cfg['proofEdges']
proof=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026\SourceOriginalTateRank.lean')
pt=proof.read_text(encoding='utf-8')
assert 'namespace Dubon2026.SourceFunctionField.OriginalChart' in pt and 'theorem original_tate_free_finite_rank' in pt
s=a.read_text(encoding='utf-8');assert s.count(old)==1
out=p/'SourceOriginalPrescribedResidualFrobeniusDependencyAudit2b.lean'
assert not out.exists();out.write_text(s.replace(old,new),encoding='utf-8')
cfg['proofEdges']=[new if n==old else n for n in cfg['proofEdges']]
co=p/'source-original-prescribed-residual-frobenius-2-audit-config-567b.json'
assert not co.exists();co.write_text(json.dumps(cfg,indent=2)+'\n',encoding='utf-8')
route=p/'prescribed-residual-frobenius-route-567.json';rd=json.loads(route.read_text(encoding='utf-8'))
rd['dependencyAuditLineage']=dict(reason='The original dependency audit used a misqualified identifier for the existing actual original Tate rank theorem. Its sole missing required name is corrected to the declaration in SourceFunctionField.OriginalChart. All 18 required dependency checks remain. No proof, public/exhaustive audit, linter scope or compiled artifact is changed.',oldIdentifier=old,correctIdentifier=new,proofSource=str(proof),proofSourceSha256=sha(proof),originalAudit=str(a),originalAuditSha256=sha(a),originalFailureLog=str(log),originalFailureLogSha256=sha(log),originalExit=1,successorAudit=str(out),successorAuditSha256=sha(out),originalConfig=str(c),originalConfigSha256=sha(c),successorConfig=str(co),successorConfigSha256=sha(co),originalRoute=str(route),originalRouteSha256=sha(route))
ro=p/'prescribed-residual-frobenius-route-567b.json';assert not ro.exists();ro.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(successor=str(out),required=len(cfg['proofEdges']),route=str(ro))))

from pathlib import Path
import ast
p=Path(__file__).parent
s=(p/'prepare_gamma_one_reduction_audit_1278.py').read_text(encoding='utf-8')
s=s.replace("r'^theorem\\s+([\\w.]+)'", 'r"^theorem\\s+([\\w.\u0027]+)"')
s=s.replace("r'^def\\s+([\\w.]+)'", 'r"^def\\s+([\\w.\u0027]+)"')
s=s.replace('source-gamma-one-reduction-1','source-gamma-one-reduction-2')
s=s.replace("('Audit1','Audit1')", "('Audit1','Audit2')")
s=s.replace("('DependencyAudit1','DependencyAudit1')", "('DependencyAudit1','DependencyAudit2')")
s=s.replace('ScratchOwnership1278','ScratchOwnership1278b')
s=s.replace('audit-route-1278','audit-route-1278b')
s=s.replace('record_gamma_one_reduction_1278','record_gamma_one_reduction_1278b')
s=s.replace('audit_gamma_one_reduction_1278.ps1','audit_gamma_one_reduction_1278b.ps1')
s=s.replace("ast.parse(s);write('record_gamma", "s=s.replace('SourceGammaOneReductionAudit1','SourceGammaOneReductionAudit2').replace('SourceGammaOneReductionDependencyAudit1','SourceGammaOneReductionDependencyAudit2')\nast.parse(s);write('record_gamma")
s=s.replace("write('audit_gamma", "s=s.replace('SourceGammaOneReductionAudit1','SourceGammaOneReductionAudit2').replace('SourceGammaOneReductionDependencyAudit1','SourceGammaOneReductionDependencyAudit2')\nwrite('audit_gamma")
ast.parse(s)
f=p/'prepare_gamma_one_reduction_audit_1278b_generated.py'
assert not f.exists()
f.write_text(s,encoding='utf-8')
exec(compile(s,str(f),'exec'))

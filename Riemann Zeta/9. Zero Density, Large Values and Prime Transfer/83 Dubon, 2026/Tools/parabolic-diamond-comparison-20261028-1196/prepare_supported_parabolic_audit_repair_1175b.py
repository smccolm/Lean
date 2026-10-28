from pathlib import Path
import ast
p=Path(__file__).parent
s=(p/'prepare_supported_parabolic_audit_1175.py').read_text(encoding='utf-8')
s=s.replace("'1172e','1173c','1174a'","'1172f','1173d','1174b'")
s=s.replace("stem='source-supported-parabolic-congruence-1'","stem='source-supported-parabolic-congruence-1b'")
s=s.replace("('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1166','ScratchOwnership1175')","('Audit1','Audit1b'),('DependencyAudit1','DependencyAudit1b'),('ScratchOwnership1166','ScratchOwnership1175b')")
s=s.replace('source-supported-parabolic-congruence-audit-route-1175','source-supported-parabolic-congruence-audit-route-1175b')
s=s.replace("No altered mathematical conclusion or raised limits.'","No altered mathematical conclusion or raised limits. The first audit found only a missing definition docstring. Its exact source and log are preserved; 1172f adds that docstring and 1173d/1174b recompile dependents.'")
s=s.replace("('ScratchOwnership1166','ScratchOwnership1175')","('ScratchOwnership1166','ScratchOwnership1175b')")
s=s.replace("ast.parse(s);write('record_supported_parabolic_congruence_1175.py',s)","s=s.replace(new+'Audit1',new+'Audit1b').replace(new+'DependencyAudit1',new+'DependencyAudit1b')\nast.parse(s);write('record_supported_parabolic_congruence_1175b.py',s)")
s=s.replace("'record_supported_parabolic_congruence_1175')","'record_supported_parabolic_congruence_1175b')")
s=s.replace("write('audit_supported_parabolic_congruence_1175.ps1',s)","s=s.replace(new+'Audit1',new+'Audit1b').replace(new+'DependencyAudit1',new+'DependencyAudit1b')\nwrite('audit_supported_parabolic_congruence_1175b.ps1',s)")
f=p/'prepare_supported_parabolic_audit_1175b.py';assert not f.exists();ast.parse(s);f.write_text(s,encoding='utf-8')

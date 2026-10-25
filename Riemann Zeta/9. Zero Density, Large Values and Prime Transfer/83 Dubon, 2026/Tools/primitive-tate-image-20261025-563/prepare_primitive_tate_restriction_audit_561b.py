from pathlib import Path
p=Path(__file__).parent
s=(p/'prepare_primitive_tate_restriction_audit_561.py').read_text(encoding='utf-8')
s=s.replace("start=s.index('  logInfo m!');end=", "start=s.index('  logInfo m!\"SOURCE ORIGINAL COEFFICIENT WEIL DEPENDENCY AUDIT PASS:');end=")
exec(compile(s,str(__file__)+' generated','exec'))

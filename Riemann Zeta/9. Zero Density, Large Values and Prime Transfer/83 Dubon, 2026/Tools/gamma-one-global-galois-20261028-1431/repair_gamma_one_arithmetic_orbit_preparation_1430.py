from pathlib import Path
p=Path(__file__).parent
s=(p/'prepare_gamma_one_arithmetic_orbit_audit_1430.py').read_text(encoding='utf-8')
s=s.replace("f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')", "f=p/n\n    if f.exists():\n        assert n in ['source-gamma-one-arithmetic-orbit-1-audit-config.json','SourceGammaOneArithmeticOrbitAudit1.lean','SourceGammaOneArithmeticOrbitDependencyAudit1.lean','SourceGammaOneArithmeticOrbitScratchOwnership1430.lean']\n        assert f.read_text(encoding='utf-8')==s,f\n    else:f.write_text(s,encoding='utf-8')")
s=s.replace("for r in rr for row in r['reuse']", "for r in rr for row in (r['reuse'] if isinstance(r['reuse'],list) else [r['reuse']])")
t=p/'prepare_gamma_one_arithmetic_orbit_audit_1430b.py';assert not t.exists();t.write_text(s,encoding='utf-8')

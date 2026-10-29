from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneGeometricArithmeticFrobenius1393b.lean';s=f.read_text(encoding='utf-8').replace('open SourceCurve CongruenceSubgroup','open SourceCurve CongruenceSubgroup IntermediateField')
t=p/'SourceGammaOneGeometricArithmeticFrobenius1393c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_geometric_arithmetic_1393b.ps1').read_text(encoding='utf-8').replace('1393b','1393c')
t=p/'build_gamma_one_geometric_arithmetic_1393c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

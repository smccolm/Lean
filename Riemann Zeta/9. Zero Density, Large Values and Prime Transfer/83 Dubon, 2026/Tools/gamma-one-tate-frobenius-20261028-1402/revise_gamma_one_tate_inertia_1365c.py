from pathlib import Path
p=Path(__file__).parent
for old,new in [('SourceGammaOneInertiaPicard1365b','SourceGammaOneInertiaPicard1365c'),('SourceGammaOneTateInertia1366b','SourceGammaOneTateInertia1366c')]:
 f=p/(old+'.lean');s=f.read_text(encoding='utf-8')
 s=s.replace('theorem reduction_arithmeticDivisor_invariant','omit [NeZero M] in\ntheorem reduction_arithmeticDivisor_invariant')
 s=s.replace('import SourceGammaOneInertiaPicard1365b','import SourceGammaOneInertiaPicard1365c')
 t=p/(new+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
 assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneInertiaPicard1365c','SourceGammaOneTateInertia1366c')")
f=p/'build_gamma_one_tate_inertia_1365c.ps1';assert not f.exists();f.write_text(s,encoding='utf-8')

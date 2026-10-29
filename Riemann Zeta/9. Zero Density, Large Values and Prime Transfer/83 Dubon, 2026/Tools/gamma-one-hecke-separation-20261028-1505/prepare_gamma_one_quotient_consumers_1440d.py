from pathlib import Path
s=Path(__file__).parent
for name,old,new,impold,impnew in [
 ('SourceGammaOneDiamondQuotientPolynomial','1439c','1439d','1438d','1438h'),
 ('SourceGammaOneDiamondQuotientHecke','1440c','1440d','1439c','1439d')]:
 f=s/(name+old+'.lean');c=f.read_text(encoding='utf-8').replace(impold,impnew)
 a=c.index('\ntheorem ',c.index('variable (Q p n w'))
 c=c[:a]+'''\nprivate local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
'''+c[a:]
 t=s/(name+new+'.lean');assert not t.exists();t.write_text(c,encoding='utf-8')
 t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_diamond_polynomial_1433.ps1').read_text(encoding='utf-8')
a=runner.index('$names=@(');b=runner.index('\nforeach',a)
runner=runner[:a]+"$names=@('SourceGammaOneDiamondQuotientPolynomial1439d','SourceGammaOneDiamondQuotientHecke1440d')"+runner[b:]
t=s/'build_gamma_one_quotient_consumers_1440d.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Updated consumers to the successful native quotient action and carrier caches.')

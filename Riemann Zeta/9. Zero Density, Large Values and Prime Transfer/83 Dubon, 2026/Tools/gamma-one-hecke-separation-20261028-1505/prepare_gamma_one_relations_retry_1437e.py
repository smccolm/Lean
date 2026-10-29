from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneTateDiamondRelations1437d.lean';c=f.read_text(encoding='utf-8')
c=c.replace('have hs := relations_stable (binaryTateDiamondOperator','have hs := relations_stable (R := ZMod N) (W := T →ₗ[ℤ_[p]] V) (I := Gamma0 M)\n    (binaryTateDiamondOperator')
t=s/'SourceGammaOneTateDiamondRelations1437e.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
for name,old,new,impold,impnew in [
 ('SourceGammaOneDiamondQuotientGalois','1438c','1438d','1437d','1437e'),
 ('SourceGammaOneDiamondQuotientPolynomial','1439b','1439c','1438c','1438d'),
 ('SourceGammaOneDiamondQuotientHecke','1440b','1440c','1439b','1439c')]:
 f=s/(name+old+'.lean');c=f.read_text(encoding='utf-8').replace(impold,impnew)
 if 'QuotientPolynomial' in name:c=c.replace('exact quotient_polynomial (binaryArithmeticTateGaloisRep','exact quotient_polynomial (R := ZMod N) (W := T →ₗ[ℤ_[p]] V)\n    (binaryArithmeticTateGaloisRep')
 t=s/(name+new+'.lean');assert not t.exists();t.write_text(c,encoding='utf-8')
 t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_quotient_1440b.ps1').read_text(encoding='utf-8')
for a,b in [('1437d','1437e'),('1438c','1438d'),('1439b','1439c'),('1440b','1440c')]:runner=runner.replace(a,b)
t=s/'build_gamma_one_quotient_1440c.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Specified the actual coefficient ring and Tate-dual module for generic inference.')

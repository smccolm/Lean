from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneTateDiamondRelations1437c.lean';c=f.read_text(encoding='utf-8')
c=c.replace('  rw [map_sub, LinearMap.congr_fun (hc i).eq x]','  have he : F (D i x) = D i (F x) := LinearMap.congr_fun (hc i).eq x\n  rw [map_sub, he]')
c=c.replace('  exact relations_stable (binaryTateDiamondOperator Q p n w)\n    (binaryArithmeticTateGaloisRep Q p n w σ)\n    (binaryTateDiamondOperator_galois_commute Q p n w σ)','  have hs := relations_stable (binaryTateDiamondOperator Q p n w)\n    (binaryArithmeticTateGaloisRep Q p n w σ)\n  have hc := binaryTateDiamondOperator_galois_commute Q p n w σ\n  have h := hs hc\n  exact h')
t=s/'SourceGammaOneTateDiamondRelations1437d.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
for name,old,new,impold,impnew in [
 ('SourceGammaOneDiamondQuotientGalois','1438b','1438c','1437c','1437d'),
 ('SourceGammaOneDiamondQuotientPolynomial','1439a','1439b','1438a','1438c'),
 ('SourceGammaOneDiamondQuotientHecke','1440a','1440b','1439a','1439b')]:
 f=s/(name+old+'.lean');c=f.read_text(encoding='utf-8').replace(impold,impnew)
 t=s/(name+new+'.lean');assert not t.exists();t.write_text(c,encoding='utf-8')
 t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_diamond_polynomial_1433.ps1').read_text(encoding='utf-8')
a=runner.index('$names=@(');b=runner.index('\nforeach',a)
names=['SourceGammaOneTateDiamondRelations1437d','SourceGammaOneDiamondQuotientGalois1438c','SourceGammaOneDiamondQuotientPolynomial1439b','SourceGammaOneDiamondQuotientHecke1440b']
runner=runner[:a]+"$names=@("+','.join(repr(x) for x in names)+')'+runner[b:]
t=s/'build_gamma_one_quotient_1440b.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Staged generic application; retained every prior source and log.')

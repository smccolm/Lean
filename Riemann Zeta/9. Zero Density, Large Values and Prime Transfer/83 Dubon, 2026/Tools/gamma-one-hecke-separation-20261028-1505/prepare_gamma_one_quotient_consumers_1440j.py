from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientPolynomial1439i.lean';c=f.read_text(encoding='utf-8')
a=c.index('  have h4 := quotient_polynomial');b=c.index('  have h5 :=',a)
c=c[:a]+'''  let q := (binaryTateDiamondRelations Q p n w).mkQ
  let F := binaryArithmeticTateGaloisRep Q p n w σ
  let Fq := binaryDiamondQuotientGaloisRep Q p n w σ
  let H := binaryTatePrimeOperators Q p n w ell
  let D := binaryTateDiamondOperator Q p n w g
  have h4 := quotient_polynomial q F Fq H D ((ell.val : ZMod N) ^ (w + 1))
'''+c[b:]
t=s/'SourceGammaOneDiamondQuotientPolynomial1439j.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=s/'SourceGammaOneDiamondQuotientHecke1440i.lean';c=f.read_text(encoding='utf-8').replace('SourceGammaOneDiamondQuotientPolynomial1439i','SourceGammaOneDiamondQuotientPolynomial1439j')
t=s/'SourceGammaOneDiamondQuotientHecke1440j.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_quotient_consumers_1440i.ps1').read_text(encoding='utf-8').replace('1439i','1439j').replace('1440i','1440j')
t=s/'build_gamma_one_quotient_consumers_1440j.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Infer carrier structures from the actual quotient map and cached operators.')

from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientPolynomial1439g.lean';c=f.read_text(encoding='utf-8')
a=c.index('theorem gammaOne_diamond_quotient_frobenius')
helper='''private theorem quotient_of_diamond (ell : sourceBinaryHeckePrime (Q * N))
    (g : Gamma0 M) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (hq : ∀ φ : T →ₗ[ℤ_[p]] V,
      binaryArithmeticTateGaloisRep Q p n w σ (binaryTatePrimeOperators Q p n w ell φ) =
        binaryArithmeticTateGaloisRep Q p n w σ (binaryArithmeticTateGaloisRep Q p n w σ φ) +
        (ell.val : ZMod N) ^ (w + 1) •
          ((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp
            (φ.comp (arithmeticDiamondTate M p g))) :
    ∀ φ : T →ₗ[ℤ_[p]] V,
      binaryDiamondQuotientGaloisRep Q p n w σ
          ((binaryTateDiamondRelations Q p n w).mkQ (binaryTatePrimeOperators Q p n w ell φ)) =
        binaryDiamondQuotientGaloisRep Q p n w σ
          (binaryDiamondQuotientGaloisRep Q p n w σ
            ((binaryTateDiamondRelations Q p n w).mkQ φ)) +
          (ell.val : ZMod N) ^ (w + 1) • (binaryTateDiamondRelations Q p n w).mkQ φ := by
'''
b=c.index('  have h4 := quotient_polynomial',a);e=c.index('\nend\n',b)
body=c[b:e].replace('d.val','σ')
new=c[:a]+helper+body+'\n'+c[a:b]+'''  exact quotient_of_diamond Q p n w ell g d.val hq
'''+c[e:]
t=s/'SourceGammaOneDiamondQuotientPolynomial1439h.lean';assert not t.exists();t.write_text(new,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=s/'SourceGammaOneDiamondQuotientHecke1440g.lean';c=f.read_text(encoding='utf-8').replace('SourceGammaOneDiamondQuotientPolynomial1439g','SourceGammaOneDiamondQuotientPolynomial1439h')
t=s/'SourceGammaOneDiamondQuotientHecke1440h.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_quotient_consumers_1440g.ps1').read_text(encoding='utf-8').replace('1439g','1439h').replace('1440g','1440h')
t=s/'build_gamma_one_quotient_consumers_1440h.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Separated the actual quotient calculation from geometric witness extraction; no proof limits changed.')

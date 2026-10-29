from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientPolynomial1439f.lean';c=f.read_text(encoding='utf-8')
a=c.index('private theorem quotient_polynomial');b=c.index('variable (Q p n w',a)
c=c[:a]+'''private theorem quotient_polynomial {R W Z : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
    (q : W →ₗ[R] Z) (F : Module.End R W) (Fq : Module.End R Z)
    (H D : Module.End R W) (a : R)
    (hc : ∀ x, Fq (q x) = q (F x))
    (hp : ∀ x, F (H x) = F (F x) + a • D x)
    (hd : ∀ x, q (D x) = q x) (x : W) :
    Fq (q (H x)) = Fq (Fq (q x)) + a • q x := by
  rw [hc, hc, hc, hp, map_add, map_smul, hd]

'''+c[b:]
a=c.index('  have h4 := quotient_polynomial');b=c.index('\nend\n',a)
c=c[:a]+'''  have h4 := quotient_polynomial (R := ZMod N) (W := T →ₗ[ℤ_[p]] V)
    (Z := (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w)
    (binaryTateDiamondRelations Q p n w).mkQ
    (binaryArithmeticTateGaloisRep Q p n w d.val) (binaryDiamondQuotientGaloisRep Q p n w d.val)
    (binaryTatePrimeOperators Q p n w ell) (binaryTateDiamondOperator Q p n w g)
    ((ell.val : ZMod N) ^ (w + 1))
  have h5 := h4 (binaryDiamondQuotientGaloisRep_mk Q p n w d.val)
  have h6 := h5 hq
  have h7 := h6 (binaryTateDiamondRelations_mk_diamond Q p n w g)
  exact h7
'''+c[b:]
t=s/'SourceGammaOneDiamondQuotientPolynomial1439g.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=s/'SourceGammaOneDiamondQuotientHecke1440f.lean';c=f.read_text(encoding='utf-8').replace('SourceGammaOneDiamondQuotientPolynomial1439f','SourceGammaOneDiamondQuotientPolynomial1439g')
c=c.replace('(R := ZMod N) (W := T →ₗ[ℤ_[p]] V)\n    (binaryTateDiamondRelations','(R := ZMod N) (W := T →ₗ[ℤ_[p]] V) (G := Qbar ≃ₐ[ℚ] Qbar)\n    (binaryTateDiamondRelations')
t=s/'SourceGammaOneDiamondQuotientHecke1440g.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_quotient_consumers_1440f.ps1').read_text(encoding='utf-8').replace('1439f','1439g').replace('1440f','1440g')
t=s/'build_gamma_one_quotient_consumers_1440g.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Reduced projection to a linear intertwining lemma and explicitly reused the actual quotient action formula.')

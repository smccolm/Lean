from pathlib import Path
s=Path(__file__).parent
base=(s/'SourceGammaOneGaloisDiamondPolynomial1436b.lean').read_text(encoding='utf-8')
vs=base[base.index('variable (Q p n w'):base.index('theorem exists_gammaOne_galois')]
sig=base[base.index('    (ell :'):base.index(' :\n    ∃ g',base.index('theorem exists_gammaOne_galois'))]
c='''import SourceGammaOneGaloisDiamondPolynomial1436b
import SourceGammaOneDiamondQuotientGalois1438a

/-! DUB-17/18 -> original all-weight association -> finite Hecke-character
quotient. Project the genuine norm-derived Frobenius polynomial through
the original diamond relations. Their generators make the diamond term
equal to one without a fixed-vector assumption. The resulting identity
uses the actual quotient Galois representation and original Hecke operator. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField

private theorem quotient_polynomial {R W G : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [Monoid G] (ρ : Representation R G W)
    (K : Submodule R W) (hK : ∀ g, K ≤ K.comap (ρ g))
    (H D : Module.End R W) (g : G) (a : R)
    (hp : ∀ x, ρ g (H x) = ρ g (ρ g x) + a • D x)
    (hd : ∀ x, K.mkQ (D x) = K.mkQ x) (x : W) :
    ρ.quotient K hK g (K.mkQ (H x)) =
      ρ.quotient K hK g (ρ.quotient K hK g (K.mkQ x)) + a • K.mkQ x := by
  change K.mkQ (ρ g (H x)) = K.mkQ (ρ g (ρ g x)) + a • K.mkQ x
  rw [hp, map_add, map_smul, hd]

'''+vs+'''theorem gammaOne_diamond_quotient_frobenius_of_degree_genus_eq
'''+sig+''' :
    ∀ φ : T →ₗ[ℤ_[p]] V,
      binaryDiamondQuotientGaloisRep Q p n w d.val
          ((binaryTateDiamondRelations Q p n w).mkQ (binaryTatePrimeOperators Q p n w ell φ)) =
        binaryDiamondQuotientGaloisRep Q p n w d.val
          (binaryDiamondQuotientGaloisRep Q p n w d.val
            ((binaryTateDiamondRelations Q p n w).mkQ φ)) +
          (ell.val : ZMod N) ^ (w + 1) • (binaryTateDiamondRelations Q p n w).mkQ φ := by
  have hs := exists_gammaOne_galois_frobenius_diamond_quadratic_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := h2 d hd hp
  obtain ⟨g, _, hq⟩ := h3
  exact quotient_polynomial (binaryArithmeticTateGaloisRep Q p n w)
    (binaryTateDiamondRelations Q p n w) (binaryTateDiamondRelations_galois Q p n w)
    (binaryTatePrimeOperators Q p n w ell) (binaryTateDiamondOperator Q p n w g)
    d.val ((ell.val : ZMod N) ^ (w + 1)) hq
    (binaryTateDiamondRelations_mk_diamond Q p n w g)

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
'''
t=s/'SourceGammaOneDiamondQuotientPolynomial1439a.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
print('Prepared actual quotient Frobenius consumer.')

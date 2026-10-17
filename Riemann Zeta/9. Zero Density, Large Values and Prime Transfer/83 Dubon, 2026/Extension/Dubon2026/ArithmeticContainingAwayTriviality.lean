import Dubon2026.ArithmeticContainingNormalizedResidual

/-! # Vanishing of actual away-prime reciprocity outside principal support

The original normalized order is zero when the rational value has valuation
one. The proved character formula kills the actual containing-field factor;
literal restriction kills the original cyclic-subfield factor. This makes
DUB-17's constructed principal support valid for the actual finite invariants.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]

/-- An actual away-prime reciprocity factor is the identity when the
original rational unit has valuation one at that prime. -/
theorem arithmeticCyclotomicContainingAwayAut_eq_one_of_valuation_eq_one
    (v : HeightOneSpectrum ℤ) (hvn : ¬Rat.HeightOneSpectrum.natGenerator v ∣ n)
    (q : ℚˣ) (hq : v.valuation ℚ q.val = 1) :
    arithmeticCyclotomicContainingAwayAut a F (Rat.HeightOneSpectrum.natGenerator v)
      (Rat.HeightOneSpectrum.prime_natGenerator v) n hvn q = 1 := by
  have horder : localFieldUnitOrder
      (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
        (Rat.HeightOneSpectrum.prime_natGenerator v))
      (Additive.ofMul
        (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v) q)) = 0 := by
    change localFieldUnitOrder
      (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
        (Rat.HeightOneSpectrum.prime_natGenerator v))
      (Additive.ofMul (Units.map
        (algebraMap ℚ (rationalPrimeLocalField
          (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom q)) = 0
    rw [rationalPrimeLocalField_rational_order]
    rw [rationalPrimePlace_of_natGenerator, hq]
    simp
  let hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  apply IsPrimitiveRoot.autToPow_injective ℚ hζ
  rw [arithmeticCyclotomicContainingAwayAut_autToPow a F
    (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v)
    n hvn q hζ, horder]
  simp

/-- The identity factor restricts to the literal original arithmetic
reciprocity value on every cyclic subfield of the containing field. -/
theorem rationalArithmeticCyclicSubfield_away_eq_one
    (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]
    (v : HeightOneSpectrum ℤ) (hvn : ¬Rat.HeightOneSpectrum.natGenerator v ∣ n)
    (q : ℚˣ) (hq : v.valuation ℚ q.val = 1) :
    rationalArithmeticFiniteLocalReciprocityAut a E (Rat.HeightOneSpectrum.natGenerator v)
      (Rat.HeightOneSpectrum.prime_natGenerator v) q = 1 := by
  let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
  have h := arithmeticCyclotomicContainingAwayAut_eq_one_of_valuation_eq_one a F n v hvn q hq
  have hr := arithmeticCyclotomicContainingAwayAut_restrict a F
    (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v)
    n hvn q E hEF
  exact hr.symm.trans ((congrArg R h).trans R.map_one)

end
end Dubon2026

import Dubon2026.ArithmeticContainingAwayTriviality

/-! # The constructed conductor-two support covers actual reciprocity factors

Away from two, removing the normalized power of two preserves the actual
containing-field factor. The proved valuation-one formula kills every
factor outside the normalized residual support, and literal restriction
kills the original cyclic-subfield value. This is the finite support
comparison needed for DUB-17's finite-plus-real carry/invariant sum.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]
    (n : ℕ) [hcycl : IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]

include hEF hcycl

/-- Every actual away-prime reciprocity factor outside the normalized
residual support is trivial on the original cyclic subfield. -/
theorem rationalTwoArithmeticCyclicSubfield_reciprocity_eq_one_of_residual_valuation
    (v : HeightOneSpectrum ℤ) (hv2 : Rat.HeightOneSpectrum.natGenerator v ≠ 2)
    (q : ℚˣ) (hv : v.valuation ℚ (rationalPrimeNormalizedResidual 2 Nat.prime_two q).val = 1) :
    rationalArithmeticFiniteLocalReciprocityAut a E (Rat.HeightOneSpectrum.natGenerator v)
      (Rat.HeightOneSpectrum.prime_natGenerator v) q = 1 := by
  have haway : ¬Rat.HeightOneSpectrum.natGenerator v ∣ 2 ^ (n + 1) := by
    intro hd
    have hp := Rat.HeightOneSpectrum.prime_natGenerator v
    exact hv2 (((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)).resolve_left hp.ne_one)
  let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
  have hzero := arithmeticCyclotomicContainingAwayAut_eq_one_of_valuation_eq_one
    a F (2 ^ (n + 1)) v haway (rationalPrimeNormalizedResidual 2 Nat.prime_two q) hv
  have hnorm := arithmeticCyclotomicContainingAwayAut_normalizedResidual a F 2 Nat.prime_two n v haway q
  have hres := arithmeticCyclotomicContainingAwayAut_restrict a F
    (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v)
    (2 ^ (n + 1)) haway q E hEF
  exact hres.symm.trans ((congrArg R hnorm.symm).trans ((congrArg R hzero).trans R.map_one))

end
end Dubon2026

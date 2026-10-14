import Dubon2026.RationalFiniteValuationUniqueness

/-! # The actual finite rational prime product

The existing finite valuation product realizes the signed exponents. The
proved rational valuation intersection identifies its absolute value with
the original rational number. Passing to positive prime generators gives
the exact rational product required by DUB-17's cyclotomic principal product.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped BigOperators

/-- The actual signed finite valuation product has the absolute value of the original rational whose valuations it realizes. -/
theorem rationalFiniteValuationProduct_abs (S : Finset (HeightOneSpectrum ℤ))
    (x : ℚ) (hx : x ≠ 0) (hS : ∀ v ∉ S, v.valuation ℚ x = 1) :
    |rationalFiniteValuationProduct S (fun v => -log (v.valuation ℚ x))| = |x| := by
  apply rational_abs_eq_of_finite_valuations _ _
    (rationalFiniteValuationProduct_ne_zero S _) hx
  intro v
  rw [rationalFiniteValuationProduct_valuation]
  by_cases hv : v ∈ S
  · rw [if_pos hv, neg_neg]
    exact exp_log ((v.valuation ℚ).ne_zero_iff.mpr hx)
  · rw [if_neg hv, hS v hv]

/-- The absolute value of the original integer prime generator is its actual positive rational prime generator. -/
theorem rationalFinitePrimeGenerator_abs (v : HeightOneSpectrum ℤ) :
    |(rationalFinitePrimeGenerator v : ℚ)| = (Rat.HeightOneSpectrum.natGenerator v : ℚ) := by
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext z
    exact map_intCast (Rat.IsIntegralClosure.intEquiv ℤ) z
  simp [Rat.HeightOneSpectrum.natGenerator, he,
    rationalFinitePrimeGenerator]
  change |((Submodule.IsPrincipal.generator v.asIdeal : ℤ) : ℚ)| =
    |((Submodule.IsPrincipal.generator (v.asIdeal.map (RingHom.id ℤ)) : ℤ) : ℚ)|
  simp only [Ideal.map_id]

/-- The original rational number is reconstructed up to sign by its actual positive prime generators and original signed valuation exponents. -/
theorem rationalPositivePrimeProduct_eq_abs (S : Finset (HeightOneSpectrum ℤ))
    (x : ℚ) (hx : x ≠ 0) (hS : ∀ v ∉ S, v.valuation ℚ x = 1) :
    (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
      (-log (v.valuation ℚ x))) = |x| := by
  have h := rationalFiniteValuationProduct_abs S x hx hS
  simpa only [rationalFiniteValuationProduct, Finset.abs_prod, abs_zpow,
    rationalFinitePrimeGenerator_abs] using h

end
end Dubon2026

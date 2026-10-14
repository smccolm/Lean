import Dubon2026.RationalFiniteValuationBasis

/-! # Original finite valuations determine a rational number up to sign

Pinned intersection of valuation integers with the original rational field
reduces a everywhere-unit rational to an actual integer unit. This identifies
the finite rational prime product needed in DUB-17's arithmetic cyclotomic
principal product, without an assumed product identity.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/-- An original rational number of value one at every finite place has absolute value one. -/
theorem rational_abs_eq_one_of_finite_valuations (x : ℚ) (hx : x ≠ 0)
    (hv : ∀ v : HeightOneSpectrum ℤ, v.valuation ℚ x = 1) : |x| = 1 := by
  obtain ⟨a, ha⟩ := mem_integers_of_valuation_le_one (R := ℤ) ℚ x
    (fun v => (hv v).le)
  obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one (R := ℤ) ℚ x⁻¹
    (fun v => by rw [map_inv₀, hv v, inv_one])
  change (a : ℚ) = x at ha
  change (b : ℚ) = x⁻¹ at hb
  have hab : a * b = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, Int.cast_one, ha, hb, mul_inv_cancel₀ hx]
  have hu : IsUnit a := IsUnit.of_mul_eq_one b hab
  rcases Int.isUnit_iff.mp hu with h | h
  · rw [← ha, h]
    norm_num
  · rw [← ha, h]
    norm_num

/-- Equal actual finite-place valuations force equal absolute values of the same original rational numbers. -/
theorem rational_abs_eq_of_finite_valuations (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : ∀ v : HeightOneSpectrum ℤ, v.valuation ℚ x = v.valuation ℚ y) : |x| = |y| := by
  have h := rational_abs_eq_one_of_finite_valuations (x / y) (div_ne_zero hx hy) (by
    intro v
    rw [map_div₀, hv v, div_self ((v.valuation ℚ).ne_zero_iff.mpr hy)])
  rw [abs_div] at h
  exact (div_eq_one_iff_eq (abs_ne_zero.mpr hy)).mp h

end
end Dubon2026

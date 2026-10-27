import Dubon2026.SourceBoundedCyclotomicLaurentGenerators
import Dubon2026.SourceBoundedCyclotomicLaurentFraction

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Fourier denominators. Every element
of the original cyclotomic j/Fricke Laurent field is a fraction of two
uniformly bounded integral-coefficient Laurent series, with nonzero
denominator. The actual generators supply the base cases; native field
adjoin induction supplies addition, multiplication and inversion. -/
namespace Dubon2026.SourceFricke
noncomputable section
open SourceFunctionField

theorem exists_bounded_fraction_frickeLaurentFieldK {N : ℕ} [NeZero N]
    {X : LaurentSeries (kN N)}
    (hX : X ∈ IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N)) :
    ∃ q r : LaurentSeries (kN N), q ≠ 0 ∧ HasBoundedIntegralLaurentCoefficients q ∧
      HasBoundedIntegralLaurentCoefficients r ∧ X * q = r := by
  have h1 : HasBoundedIntegralLaurentCoefficients (1 : LaurentSeries (kN N)) := by
    simpa only [map_one] using
      (hasBoundedIntegralLaurentCoefficients_integer_map (K := kN N) 1)
  have h0 : HasBoundedIntegralLaurentCoefficients (0 : LaurentSeries (kN N)) := by
    simpa only [map_zero] using
      (hasBoundedIntegralLaurentCoefficients_integer_map (K := kN N) 0)
  induction hX using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl⟩
    · exact ⟨1, jqNModC (kN N) N, one_ne_zero, h1,
        hasBoundedIntegralLaurentCoefficients_jqNModC (kN N) N, mul_one _⟩
    · exact exists_bounded_frickeLaurentK_fraction N i
  | algebraMap c =>
    refine ⟨1, algebraMap (kN N) (LaurentSeries (kN N)) c, one_ne_zero, h1, ?_, mul_one _⟩
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt]
    exact hasBoundedIntegralLaurentCoefficients_single_zero_kN N c
  | add x y _ _ hx hy =>
    obtain ⟨q, r, hq0, hq, hr, he⟩ := hx
    obtain ⟨p, s, hp0, hp, hs, hf⟩ := hy
    refine ⟨q * p, r * p + s * q, mul_ne_zero hq0 hp0, hq.mul hp,
      (hr.mul hp).add (hs.mul hq), ?_⟩
    calc (x + y) * (q * p) = (x * q) * p + (y * p) * q := by ring
      _ = r * p + s * q := by rw [he, hf]
  | inv x _ hx =>
    obtain ⟨q, r, hq0, hq, hr, he⟩ := hx
    by_cases hx0 : x = 0
    · exact ⟨1, 0, one_ne_zero, h1, h0, by rw [hx0, inv_zero, zero_mul]⟩
    · have hr0 : r ≠ 0 := by rw [← he]; exact mul_ne_zero hx0 hq0
      refine ⟨r, q, hr0, hr, hq, ?_⟩
      rw [← he, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x y _ _ hx hy =>
    obtain ⟨q, r, hq0, hq, hr, he⟩ := hx
    obtain ⟨p, s, hp0, hp, hs, hf⟩ := hy
    refine ⟨q * p, r * s, mul_ne_zero hq0 hp0, hq.mul hp, hr.mul hs, ?_⟩
    calc x * y * (q * p) = (x * q) * (y * p) := by ring
      _ = r * s := by rw [he, hf]

end
end Dubon2026.SourceFricke

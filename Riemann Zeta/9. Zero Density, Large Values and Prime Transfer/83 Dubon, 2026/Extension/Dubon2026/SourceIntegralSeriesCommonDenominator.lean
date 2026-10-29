import Dubon2026.SourceIntegralSeriesScalarDescent
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Integral

/-! DUB-17/18 -> original Gamma1 degree/genus -> uniform level-power
slash integrality -> common integer denominator. A finite complex
combination of integer series with algebraic coefficients admits one
nonzero integer clearing all its coefficients. The proved scalar
projection descends the finite combination; Mathlib's finite integral
multiple theorem clears its actual algebraic scalars. This is the
required algebraic step for the existing integral cusp-form span. -/
namespace Dubon2026.SourceFunctionField.IntegralFricke
noncomputable section

theorem exists_common_integer_denominator_of_integral_series_sum
    {ι : Type*} [Fintype ι] (g : ι → PowerSeries ℤ) (c : ι → ℂ)
    (h : ∀ m : ℕ, IsAlgebraic ℚ
      ((∑ i, c i • (g i).map (Int.castRingHom ℂ)).coeff m)) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ m : ℕ, IsIntegral ℤ
      ((d : ℂ) * (∑ i, c i • (g i).map (Int.castRingHom ℂ)).coeff m) := by
  classical
  let K := algebraicClosure ℚ ℂ
  letI : Algebra.IsAlgebraic ℚ K := algebraicClosure.isAlgebraic ℚ ℂ
  obtain ⟨c', hc', heq⟩ := exists_sum_smul_eq_of_forall_coeff_mem K.toSubfield
    (fun i => (g i).map (Int.castRingHom ℂ))
    (fun i m => by simp only [PowerSeries.coeff_map, Int.coe_castRingHom]; exact intCast_mem _ _)
    c (fun m => mem_algebraicClosure_iff.mpr (h m))
  let cc : ι → K := fun i => ⟨c' i, hc' i⟩
  letI := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  letI := Algebra.IsAlgebraic.trans ℤ ℚ K
  obtain ⟨d, hd, hD⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image cc)
  have hdi (i : ι) : IsIntegral ℤ ((d : ℂ) * c' i) := by
    have hi := hD (cc i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    simpa only [map_smul, zsmul_eq_mul] using hi.algebraMap (B := ℂ)
  refine ⟨d, hd, fun m => ?_⟩
  rw [← heq, map_sum, Finset.mul_sum]
  apply IsIntegral.sum
  intro i _
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_map, smul_eq_mul, ← mul_assoc]
  exact (hdi i).mul (isIntegral_algebraMap : IsIntegral ℤ (((g i).coeff m : ℤ) : ℂ))

end
end Dubon2026.SourceFunctionField.IntegralFricke

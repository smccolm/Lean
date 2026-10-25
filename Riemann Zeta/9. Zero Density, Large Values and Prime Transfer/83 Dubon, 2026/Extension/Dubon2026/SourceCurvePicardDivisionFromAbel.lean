import Dubon2026.SourceCurvePicardDivisionFromPrincipal
import Dubon2026.SourcePeriodDivision

/-! DUB-17/18 -> auxiliary point division. The exact two proved Abel inputs
give division in the actual Picard quotient. Keeping their additive deduction
at the function-field level avoids expanding the concrete cover field. -/
namespace Dubon2026.SourceCurve.Pic0
noncomputable section
variable {K F ι : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_nsmul_mk_of_abel_data (n : ℕ) (hn : n ≠ 0)
    (AJ : Divisor K F →+ (ι → ℂ)) (Λ : Submodule ℤ (ι → ℂ))
    (hinv : ∀ u : ι → ℂ, ∃ B : Divisor K F,
      Divisor.degree B = 0 ∧ AJ B - u ∈ Λ)
    (hker : ∀ B : Divisor K F, Divisor.degree B = 0 → AJ B ∈ Λ → Divisor.IsPrincipal B)
    (D : Divisor.degZero (K := K) (F := F)) :
    ∃ y : Pic0 K F, n • y = mk D := by
  obtain ⟨B, hB0, hB⟩ := hinv ((n : ℂ)⁻¹ • AJ D.val)
  have hD0 : Divisor.degree D.val = 0 := D.property
  have hzero : Divisor.degree (n • B - D.val) = 0 := by
    rw [map_sub, map_nsmul, hB0, hD0, nsmul_zero, sub_self]
  have hperiod : AJ (n • B - D.val) ∈ Λ := by
    rw [map_sub, map_nsmul]
    exact SourceFunctionField.PeriodDivision.integer_multiple_mem_of_scaled_difference
      Λ n hn (AJ B) (AJ D.val) hB
  exact exists_nsmul_mk_of_principal_difference n D B hB0 (hker _ hzero hperiod)

end
end Dubon2026.SourceCurve.Pic0

import Dubon2026.SourceOriginalCuspDimension
import Dubon2026.SourceParabolicGenusBound

/-! DUB-17/18 -> actual parabolic Hecke realization.
The missing geometric dimension bound is now proved on original regular
differentials. Together with the existing period injection and Manin bound,
it proves surjectivity of the actual original weight-two period pair.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup SourceCuspBoundary SourceFunctionField

theorem sourceWeightTwoParabolic_dimension_eq (N : ℕ) [NeZero N] :
    Module.finrank ℂ (parabolicHoms N) =
      2 * Module.finrank ℂ (CuspForm (Gamma0 N) 2) := by
  have hlo := sourceWeightTwoPeriod_dimension_lower N
  have hhi := sourceParabolic_dimension_le_two_mul_genusFormula N
  have hg := genusFormula_le_finrank_cuspForms N
  have hq : (Module.finrank ℂ (parabolicHoms N) : ℚ) ≤
      2 * (Module.finrank ℂ (CuspForm (Gamma0 N) 2) : ℚ) := by linarith
  apply Nat.le_antisymm
  · exact_mod_cast hq
  · exact hlo

theorem sourceWeightTwo_cusp_dimension_eq_genusFormula (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (CuspForm (Gamma0 N) 2) : ℚ) = SourceLevelProjective.genusFormula N := by
  have hhi := sourceParabolic_dimension_le_two_mul_genusFormula N
  rw [sourceWeightTwoParabolic_dimension_eq N] at hhi
  push_cast at hhi
  have hlo := genusFormula_le_finrank_cuspForms N
  linarith

theorem sourceWeightTwoParabolicPeriodPair_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (sourceWeightTwoParabolicPeriodPair N) := by
  letI := original_weight_two_cusp_finite N
  letI := sourceWeightTwoParabolic_finite N
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := sourceWeightTwoParabolicPeriodPair N) ?_).mp
    (sourceWeightTwoParabolicPeriodPair_injective N)
  rw [Module.finrank_prod, sourceWeightTwoParabolic_dimension_eq N, two_mul]

/-- The actual original period pair is an isomorphism onto the parabolic space. -/
def sourceWeightTwoParabolicPeriodEquiv (N : ℕ) [NeZero N] :
    (CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) ≃ₗ[ℂ] parabolicHoms N :=
  LinearEquiv.ofBijective (sourceWeightTwoParabolicPeriodPair N)
    ⟨sourceWeightTwoParabolicPeriodPair_injective N, sourceWeightTwoParabolicPeriodPair_surjective N⟩

theorem sourceWeightTwoParabolicPeriodEquiv_apply (N : ℕ) [NeZero N]
    (f : CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) :
    sourceWeightTwoParabolicPeriodEquiv N f = sourceWeightTwoParabolicPeriodPair N f := rfl

end
end Dubon2026

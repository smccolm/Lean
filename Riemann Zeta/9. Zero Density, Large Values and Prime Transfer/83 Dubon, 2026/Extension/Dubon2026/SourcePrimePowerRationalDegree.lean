import Dubon2026.SourcePrimePowerRelativeStep
import Dubon2026.SourceOriginalPrimeDegree

/-! DUB-17/18 -> numerical modular genus -> exact original j-map degree.
The prime base degree and the proved degree-p tower steps give the full
rational prime-power degree by native multiplicativity of relative degree.
Finiteness and coefficient transport were proved for the original field.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem original_prime_rational_relfinrank (p : ℕ) [Fact p.Prime] :
    relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (modularFunctionFieldFull p) = p + 1 :=
  (finrank_original_over_j_baseChange p (AlgebraicClosure ℚ)).symm.trans
    (finrank_original_over_j_prime p (AlgebraicClosure ℚ))

theorem original_prime_power_rational_relfinrank (p : ℕ) [Fact p.Prime] (k : ℕ) :
    relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (modularFunctionFieldFull (p ^ (k + 1))) = p ^ k * (p + 1) := by
  induction k with
  | zero => simpa only [zero_add, pow_one, pow_zero, one_mul] using original_prime_rational_relfinrank p
  | succ k ih =>
    have hj : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤
        modularFunctionFieldFull (p ^ (k + 1)) :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_full _))
    have h := relfinrank_mul_relfinrank hj (original_prime_power_fields_mono p (k + 1))
    rw [ih, original_prime_power_step_relfinrank] at h
    rw [← h, pow_succ]
    ring

end
end Dubon2026.SourceFunctionField

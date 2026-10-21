import Dubon2026.SourceOriginalPrimePowerFields
import Dubon2026.SourcePrimePowerExactFieldDegree

/-! DUB-17/18 -> numerical modular genus -> exact original j-map degree.
The literal prime-power extension has degree p. The previous nonmembership
premise is discharged by the original tower argument, whose base case
uses proved integral-root descent and nonpolynomiality of j(q^p).
-/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem original_prime_power_step_finrank_eq (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Module.finrank (modularFunctionFieldFull (p ^ (k + 1)))
      (IntermediateField.adjoin (modularFunctionFieldFull (p ^ (k + 1)))
        ({qExpand ℚ (p ^ (k + 2)) jq} : Set (LaurentSeries ℚ))) = p :=
  original_prime_power_step_finrank_eq_of_not_mem p k (original_prime_power_next_not_mem p k)

end
end Dubon2026.SourceFunctionField

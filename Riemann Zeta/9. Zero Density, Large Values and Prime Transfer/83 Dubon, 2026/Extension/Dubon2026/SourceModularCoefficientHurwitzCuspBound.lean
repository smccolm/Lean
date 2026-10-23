import Dubon2026.SourceModularCoefficientHurwitzNumeric
import Dubon2026.SourceModularCoefficientCuspCount

/-! DUB-17/18 -> good reduction -> reverse genus inequality. The actual
cusp count removes the supplied pole set and its cardinality from the
Hurwitz inequalities. Only the selected finite contribution remains. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential SourceLevelProjective
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

theorem coeff_hurwitz_differential_cusp_bound (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v ∈ S, 0 ≤ v.ord (jCoeff N K)) :
    (∑ v ∈ S, v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K))) ≤
      2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 +
        (dedekindPsi N : ℤ) + (cuspCount N : ℤ) := by
  classical
  have hp : {v : Place K (modularFunctionFieldCoeff N K) | v.ord (jCoeff N K) < 0}.Finite :=
    (finite_coeff_divisor_support N K (jCoeff N K)).subset fun _ hv => ne_of_lt hv
  have h := coeff_hurwitz_differential_numeric N K hNK S hS hp.toFinset
    (fun v => hp.mem_toFinset)
  rw [card_coeff_j_poles_eq_cuspCount N K hNK hp.toFinset
    (fun v => hp.mem_toFinset)] at h
  omega

theorem coeff_hurwitz_ramification_cusp_bound (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (a : Place K (modularFunctionFieldCoeff N K) → K)
    (hS : ∀ v ∈ S, 0 < v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) (a v))) :
    (∑ v ∈ S, (v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) (a v)) - 1)) ≤
      2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 +
        (dedekindPsi N : ℤ) + (cuspCount N : ℤ) := by
  classical
  have hp : {v : Place K (modularFunctionFieldCoeff N K) | v.ord (jCoeff N K) < 0}.Finite :=
    (finite_coeff_divisor_support N K (jCoeff N K)).subset fun _ hv => ne_of_lt hv
  have h := coeff_hurwitz_ramification_numeric N K hNK S a hS hp.toFinset
    (fun v => hp.mem_toFinset)
  rw [card_coeff_j_poles_eq_cuspCount N K hNK hp.toFinset
    (fun v => hp.mem_toFinset)] at h
  omega

end
end Dubon2026.SourceFunctionField

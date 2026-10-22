import Dubon2026.SourceOriginalAbelJacobiPeriods
import Dubon2026.SourceOriginalFiberOrderSupport

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel. A principal divisor is the difference of the zero fibers
of f and its reciprocal; their fibers over one agree with multiplicity.
Existing normalized-order addition and pole invariance give that identity.
No new local-ring unit or valuation construction is needed.
Adapted from S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- The effective zero divisor of the actual original function. -/
def originalZeroDivisor (f : F) : Divisor ℂ F := originalPrincipalDivisor N ℂ f ⊔ 0

theorem originalZeroDivisor_apply (f : F) (v : Place ℂ F) :
    originalZeroDivisor N f v = max (v.ord f) 0 := by
  rw [originalZeroDivisor, Finsupp.sup_apply]
  rfl

omit [NeZero N] in
theorem original_max_ord_sub_one_eq (v : Place ℂ F) (f : F) :
    max (v.ord (f - 1)) 0 = max (v.ord (f⁻¹ - 1)) 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  rcases eq_or_ne f 1 with rfl | hf1
  · simp
  have hkey : v.ord (f⁻¹ - 1) = v.ord (f - 1) - v.ord f := by
    have he : f⁻¹ - 1 = -(f - 1) * f⁻¹ := by field_simp; ring
    rw [he, v.ord_mul (neg_ne_zero.mpr (sub_ne_zero.mpr hf1)) (inv_ne_zero hf0),
      v.ord_neg, v.ord_inv]
    ring
  rw [hkey]
  rcases lt_trichotomy (v.ord f) 0 with hlt | heq | hgt
  · have hp : f ∉ v.toValuationSubring := fun hm => (not_lt_of_ge (v.ord_nonneg_of_mem hm)) hlt
    have ho := original_ord_sub_const_of_pole N v hp (1 : ℂ)
    simp only [map_one] at ho
    rw [ho]
    omega
  · rw [heq, sub_zero]
  · have h0 : v.ord (f - 1) = 0 := by
      have ha := v.ord_add_eq_of_lt (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) hf0
        (by rw [v.ord_neg, v.ord_one]; exact hgt)
      rw [show f - 1 = -1 + f from by ring, ha, v.ord_neg, v.ord_one]
    rw [h0]
    omega

theorem original_principal_zero_difference (f : F) :
    originalPrincipalDivisor N ℂ f = originalZeroDivisor N f - originalZeroDivisor N f⁻¹ := by
  ext v
  rw [Finsupp.sub_apply, originalZeroDivisor_apply, originalZeroDivisor_apply, v.ord_inv]
  change v.ord f = max (v.ord f) 0 - max (-v.ord f) 0
  omega

theorem original_zero_fiber_one_eq (f : F) :
    originalZeroDivisor N (f - 1) = originalZeroDivisor N (f⁻¹ - 1) := by
  ext v
  rw [originalZeroDivisor_apply, originalZeroDivisor_apply]
  exact original_max_ord_sub_one_eq N v f

end
end Dubon2026.SourceFunctionField.OriginalChart

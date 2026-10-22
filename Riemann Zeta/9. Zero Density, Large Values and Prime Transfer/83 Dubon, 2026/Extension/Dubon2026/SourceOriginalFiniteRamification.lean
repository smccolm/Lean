import Dubon2026.SourceOriginalAnalyticJMultiplicity

/-! DUB-17/18 -> numerical modular genus -> absence of other finite
ramification. Every actual finite place is analytic. At values different
from zero and 1728 the analytic j-order is one, so the original discrete
place order is one as well. Both realization and local multiplicity are
proved inputs, with no ramification hypothesis in the conclusion.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

theorem original_analytic_generic_j_order (N : ℕ) [NeZero N] (τ : ℍ)
    (h4 : ModularForm.E₄ τ ≠ 0) (h6 : ModularForm.E₆ τ ≠ 0) :
    (originalAnalyticPlace N τ).ord (jOver N ℂ -
      algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) = 1 := by
  have hm := original_analytic_j_multiplicity N τ
  rw [(JMultiplicity.case_generic h4 h6).2] at hm
  have hi : (originalAnalyticRamification N τ : ℤ) *
      (originalAnalyticPlace N τ).ord (jOver N ℂ -
        algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) = 1 := by
    exact WithTop.coe_injective hm
  have he : 0 < (originalAnalyticRamification N τ : ℤ) :=
    Int.natCast_pos.mpr (originalAnalyticRamification_pos N τ)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hi with h | h
  · rwa [h, one_mul] at hi
  · omega

theorem original_finite_j_fiber_order_one (N : ℕ) [NeZero N]
    (P : SourceCurve.Place ℂ (modularFunctionFieldOver N ℂ)) (c : ℂ)
    (hc0 : c ≠ 0) (hc1728 : c ≠ 1728)
    (hP : 0 < P.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c)) :
    P.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) = 1 := by
  obtain ⟨τ, hτ, hj⟩ := original_finite_fiber_realization N P c hP
  have h4 : ModularForm.E₄ τ ≠ 0 := by
    intro hz
    apply hc0
    rw [← hj, hz, zero_pow (by decide : 3 ≠ 0), zero_div]
  have h6 : ModularForm.E₆ τ ≠ 0 := by
    intro hz
    exact hc1728 (hj.symm.trans (JMultiplicity.jf_eq_of_E₆_eq_zero hz))
  have h := original_analytic_generic_j_order N τ h4 h6
  change (originalAnalyticPlace N τ).ord (jOver N ℂ -
    algebraMap ℂ (modularFunctionFieldOver N ℂ)
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)) = 1 at h
  rwa [hτ, hj] at h

end
end Dubon2026.SourceFunctionField

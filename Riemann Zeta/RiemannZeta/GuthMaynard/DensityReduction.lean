import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.SymmetryTransfer

open Complex

namespace RiemannZeta.GuthMaynard

/-- Symmetry-informed density reduction (F-14).
    Under the Functional Symmetry Hypothesis, the number of zeros `N(σ, T)` 
    is bounded related to `N(1-σ, T)`. -/
def SymmetricDensityReductionProp (model : ZetaZeroCountModel) : Prop :=
  ∀ (σ T : ℝ), 1/2 < σ → σ ≤ 1 → N model σ T ≤ N model (1 - σ) T

/-- F-13 implies F-14: The Functional Symmetry Hypothesis implies 
    the symmetric density reduction property. -/
theorem functional_symmetry_implies_reduction (model : ZetaZeroCountModel) 
    (h_sym : FunctionalSymmetryHypothesis model) : 
    SymmetricDensityReductionProp model := by
  intro σ T h_half_lt h_le_one
  have h_le : 1 - σ ≤ σ := by linarith
  unfold N zeroCountRect
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s
    rw [zerosInRect, zerosInRect, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, 
        Set.mem_inter_iff, Set.mem_inter_iff, ZeroRectangle, ZeroRectangle, 
        Set.mem_setOf_eq, Set.mem_setOf_eq]
    rintro ⟨⟨hσ, hs1, ht1, ht2⟩, hz⟩
    exact ⟨⟨le_trans h_le hσ, hs1, ht1, ht2⟩, hz⟩
  · intro i _ _
    exact Nat.zero_le _

end RiemannZeta.GuthMaynard

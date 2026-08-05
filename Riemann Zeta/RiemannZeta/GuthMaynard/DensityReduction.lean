import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.SymmetryTransfer

open Complex

namespace RiemannZeta.GuthMaynard

/-- Monotonic density reduction (F-14).
    The number of zeros `N(σ, T)` is monotonically bounded by `N(1-σ, T)` for `σ ≥ 1/2` 
    simply because the region `Re(s) ≥ σ` is a subset of `Re(s) ≥ 1-σ`. 
    This is an ordinary set monotonicity consequence, not dependent on functional symmetry. -/
def MonotonicDensityReductionProp (model : ZetaZeroCountModel) : Prop :=
  ∀ (σ T : ℝ), 1/2 < σ → σ ≤ 1 → N model σ T ≤ N model (1 - σ) T

/-- F-13/F-14: Set monotonicity of the zero count. -/
theorem monotonic_density_reduction (model : ZetaZeroCountModel) : 
    MonotonicDensityReductionProp model := by
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

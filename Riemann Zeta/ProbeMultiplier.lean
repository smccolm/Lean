import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_multiplier
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (n : ℕ) :
    ‖dfiEquation29BranchShiftSign branch *
        ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)‖ =
      ((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ) := by
  cases branch <;>
    simp [dfiEquation29BranchShiftSign,
      Real.norm_of_nonneg Real.pi_pos.le]

end RiemannZeta.GuthMaynard

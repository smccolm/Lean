import GafniTao.PintzZetaAFETermShift

/-!
# Finite-head displacement in the single-zeta AFE

This module performs the first series-level contour displacement.  At every
finite height the original right-edge series is split into a finite positive
head and its literal complement.  Only the head is moved to the left.  Thus no
convergence of an individual improper tail is assumed.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace GafniTao

noncomputable section

/-- The termwise vertical truncation is exactly the normalized integral of the
opened right-edge term. -/
theorem pintzZetaAFETermVerticalTrunc_eq_rightTerm
    (s base : ℂ) (n : ℕ) (r H : ℝ) :
    pintzZetaAFETermVerticalTrunc s base n r H =
      (1 / (2 * Real.pi : ℂ)) *
        ∫ u in -H..H, pintzZetaAFERightTerm s base r u n := by
  unfold pintzZetaAFETermVerticalTrunc
  have hcoef : (((1 / (2 * Real.pi) : ℝ) : ℂ)) =
      1 / (2 * Real.pi : ℂ) := by
    push_cast
    rfl
  rw [hcoef]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _hu
  exact pintzZetaAFETermContourIntegrand_vertical s base n r u

/-- At a finite height the normalized term integrals form a summable series
on every genuine Dirichlet-series right line. -/
theorem summable_pintzZetaAFETermVerticalTrunc
    (s base : ℂ) (c H : ℝ) (hc : 1 < base.re + c) (hc0 : c ≠ 0) :
    Summable (fun n : ℕ => pintzZetaAFETermVerticalTrunc s base n c H) := by
  have hint : Summable (fun n : ℕ =>
      ∫ u in -H..H, pintzZetaAFERightTerm s base c u n) :=
    (intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (summable_pintzZetaAFERight_restrict_norm s base c H hc hc0)).summable
  have hscaled := hint.mul_left (1 / (2 * Real.pi : ℂ))
  simpa only [← pintzZetaAFETermVerticalTrunc_eq_rightTerm] using hscaled

/-- Exact finite-height splitting into a selected head and the literal
subtype-indexed complement. -/
theorem pintzZetaAFETermVerticalTrunc_sum_add_compl
    (s base : ℂ) (S : Finset ℕ) (c H : ℝ)
    (hc : 1 < base.re + c) (hc0 : c ≠ 0) :
    (∑ n ∈ S, pintzZetaAFETermVerticalTrunc s base n c H) +
        ∑' n : {n : ℕ // n ∉ S},
          pintzZetaAFETermVerticalTrunc s base n.1 c H =
      ∑' n : ℕ, pintzZetaAFETermVerticalTrunc s base n c H := by
  exact (summable_pintzZetaAFETermVerticalTrunc s base c H hc hc0).sum_add_tsum_compl

/-- Series-level finite-head displacement.  The complement stays on the
original right line, and the difference converges to the exact sum of the
residues of the selected positive coefficients. -/
theorem tendsto_pintzZetaAFERightSeries_displaced_finset
    (s base : ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0)
    {q c : ℝ} (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re)
    (hright : 1 < base.re + c) :
    Tendsto (fun H : ℝ =>
      (∑' n : ℕ, pintzZetaAFETermVerticalTrunc s base n c H) -
        ((∑ n ∈ S, pintzZetaAFETermVerticalTrunc s base n (-q) H) +
          ∑' n : {n : ℕ // n ∉ S},
            pintzZetaAFETermVerticalTrunc s base n.1 c H))
      atTop (nhds (∑ n ∈ S, pintzZetaAFETermNumerator s base n 0)) := by
  have hhead := tendsto_pintzZetaAFETerm_vertical_difference_finset
    s base S hS hq hc hbase
  apply hhead.congr'
  filter_upwards with H
  have hsplit := pintzZetaAFETermVerticalTrunc_sum_add_compl
    s base S c H hright (ne_of_gt hc)
  rw [Finset.sum_sub_distrib]
  linear_combination hsplit

#print axioms pintzZetaAFETermVerticalTrunc_eq_rightTerm
#print axioms summable_pintzZetaAFETermVerticalTrunc
#print axioms pintzZetaAFETermVerticalTrunc_sum_add_compl
#print axioms tendsto_pintzZetaAFERightSeries_displaced_finset

end

end GafniTao

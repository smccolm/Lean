import RiemannZeta.GuthMaynard.DFIDelta
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of the DFI delta kernel

The finite radius in `dfiDeltaKernel` depends discontinuously on the argument,
but all terms that enter or leave the displayed finite sum are already zero.
This file proves smoothness by replacing the kernel locally by one fixed finite
sum.  This is the regularity input suppressed when DFI applies Voronoi
summation to equation (22).
-/

open Complex Finset Set Filter Topology
open scoped BigOperators ContDiff Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-- One summand in the infinite-series form of the DFI delta kernel. -/
noncomputable def dfiDeltaSummand {Q : ℝ} (w : DFIDeltaWeight Q)
    (q r : ℕ) (u : ℝ) : ℝ :=
  (w ((q * r : ℕ) : ℝ) - w (u / (q * r : ℕ))) / (q * r : ℕ)

theorem contDiff_dfiDeltaSummand {Q : ℝ} (w : DFIDeltaWeight Q)
    (q r : ℕ) : ContDiff ℝ ∞ (dfiDeltaSummand w q r) := by
  unfold dfiDeltaSummand
  have harg : ContDiff ℝ ∞ (fun u : ℝ => u / (q * r : ℕ)) := by fun_prop
  exact (contDiff_const.sub (w.smooth.comp harg)).div_const _

/-- On a unit neighborhood of `u₀`, one fixed radius contains every
nonzero summand. -/
theorem dfiDeltaSummand_eq_zero_eventually_outside
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q) (u₀ : ℝ) :
    ∀ᶠ u in nhds u₀, ∀ r : ℕ,
      r ∉ Finset.Icc 1 (⌈2 * Q + (|u₀| + 1) / Q⌉₊ + 1) →
        dfiDeltaSummand w q r u = 0 := by
  filter_upwards [Metric.ball_mem_nhds u₀ (by norm_num : (0 : ℝ) < 1)] with u hu
  intro r hr
  simp only [Finset.mem_Icc, not_and_or, not_le] at hr
  rcases hr with hrzero | hrlarge
  · have hr0 : r = 0 := by omega
    simp [dfiDeltaSummand, hr0]
  · have habs : |u| < |u₀| + 1 := by
      have hdist : |u - u₀| < 1 := by simpa [Real.dist_eq] using hu
      calc
        |u| = |(u - u₀) + u₀| := by ring_nf
        _ ≤ |u - u₀| + |u₀| := abs_add_le _ _
        _ < |u₀| + 1 := by linarith
    have hinside : dfiDeltaRadius Q u ≤
        ⌈2 * Q + (|u₀| + 1) / Q⌉₊ + 1 := by
      unfold dfiDeltaRadius
      have hdiv : |u| / Q ≤ (|u₀| + 1) / Q :=
        (div_le_div_iff_of_pos_right w.Q_pos).2 habs.le
      have hbase : 2 * Q + |u| / Q ≤
          2 * Q + (|u₀| + 1) / Q := by linarith
      exact Nat.add_le_add_right
        (Nat.ceil_mono hbase) 1
    have hradius : dfiDeltaRadius Q u ≤ q * r := by
      have hrle : ⌈2 * Q + (|u₀| + 1) / Q⌉₊ + 1 ≤ r :=
        Nat.le_of_lt hrlarge
      exact hinside.trans (hrle.trans (Nat.le_mul_of_pos_left r hq))
    have hqr : 0 < q * r := Nat.mul_pos hq (by omega)
    obtain ⟨hfirst, hsecond⟩ :=
      dfiDeltaWeight_pair_eq_zero_of_radius_le w (q * r) hqr hradius
    rw [dfiDeltaSummand, hfirst, hsecond]
    simp

/-- The finite implementation of the DFI delta kernel is smooth in its real
argument for every positive modulus. -/
theorem contDiff_dfiDeltaKernel {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (hq : 0 < q) : ContDiff ℝ ∞ (dfiDeltaKernel w q) := by
  rw [contDiff_iff_contDiffAt]
  intro u₀
  let R : ℕ := ⌈2 * Q + (|u₀| + 1) / Q⌉₊ + 1
  let fixed : ℝ → ℝ := fun u =>
    ∑ r ∈ Finset.Icc 1 R, dfiDeltaSummand w q r u
  have hfixed : ContDiff ℝ ∞ fixed := by
    dsimp [fixed]
    exact ContDiff.sum fun r _ => contDiff_dfiDeltaSummand w q r
  have heq : dfiDeltaKernel w q =ᶠ[nhds u₀] fixed := by
    filter_upwards [dfiDeltaSummand_eq_zero_eventually_outside w q hq u₀] with u hu
    rw [dfiDeltaKernel_eq_tsum w q hq u]
    change (∑' r : ℕ, dfiDeltaSummand w q r u) = fixed u
    rw [tsum_eq_sum (s := Finset.Icc 1 R) (fun r hr => by
      apply hu r
      simpa [R] using hr)]
  exact hfixed.contDiffAt.congr_of_eventuallyEq heq

end RiemannZeta.GuthMaynard

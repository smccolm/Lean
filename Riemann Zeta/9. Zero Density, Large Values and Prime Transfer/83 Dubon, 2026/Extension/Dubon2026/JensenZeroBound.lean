import Dubon2026.DirichletDivisor
import Dubon2026.TwistProductStrip
import Mathlib.Analysis.Complex.JensenFormula

/-! # Jensen bounds for finite sets of actual zeros with analytic multiplicity -/

namespace Dubon2026

open Complex Set Metric MeromorphicOn
open scoped BigOperators

theorem sum_zeroMultiplicity_le_sum_divisor {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} {r : ℝ} {S : Finset ℂ}
    (hS : ∀ s ∈ S, s ∈ closedBall c r ∧ dirichletSum a N s = 0) :
    (∑ s ∈ S, (zeroMultiplicity a N s : ℤ)) ≤
      ∑ᶠ s, MeromorphicOn.divisor (dirichletSum a N) (closedBall c r) s := by
  classical
  let D := MeromorphicOn.divisor (dirichletSum a N) (closedBall c r)
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c r)
  have hsub : S ⊆ hfin.toFinset := by
    intro s hs
    exact hfin.mem_toFinset.mpr ((mem_dirichlet_divisor_support hN ha _ s).mpr (hS s hs))
  have hnonneg : 0 ≤ D :=
    (analyticOnNhd_dirichletSum a N |>.mono (subset_univ (closedBall c r))).divisor_nonneg
  calc
    _ = ∑ s ∈ S, D s := by
      apply Finset.sum_congr rfl
      intro s hs
      exact (dirichlet_divisor_apply hN ha (hS s hs).1).symm
    _ ≤ ∑ s ∈ hfin.toFinset, D s :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => hnonneg s)
    _ = ∑ᶠ s, D s := (finsum_eq_sum D hfin).symm

theorem sum_zeroMultiplicity_le_jensen {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} {r R B : ℝ} {S : Finset ℂ}
    (hr : 0 < r) (hrR : r < R) (hB : 1 ≤ B) (hc : dirichletSum a N c ≠ 0)
    (hS : ∀ s ∈ S, s ∈ closedBall c r ∧ dirichletSum a N s = 0)
    (hb : ∀ s ∈ sphere c R, ‖dirichletSum a N s‖ ≤ B) :
    (∑ s ∈ S, (zeroMultiplicity a N s : ℝ)) ≤
      Real.log (B / ‖dirichletSum a N c‖) / Real.log (R / r) := by
  have hle := sum_zeroMultiplicity_le_sum_divisor hN ha hS
  have hsum : (∑ s ∈ S, (zeroMultiplicity a N s : ℝ)) ≤
      ((∑ᶠ s, MeromorphicOn.divisor (dirichletSum a N) (closedBall c r) s : ℤ) : ℝ) := by
    exact_mod_cast hle
  apply hsum.trans
  have hR : 0 < R := hr.trans hrR
  have hj :=
    (analyticOnNhd_dirichletSum a N |>.mono (subset_univ (closedBall c |R|))).sum_divisor_le
      (r := r)
      (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR) hB hc
      (by simpa only [abs_of_pos hR] using hb)
  rw [abs_of_pos hr] at hj
  exact hj

theorem norm_dirichletSum_le_ball_majorant (a : ℕ → ℂ) (N : ℕ)
    {c s : ℂ} {R : ℝ} (hs : s ∈ closedBall c R) :
    ‖dirichletSum a N s‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ * Real.exp (-(c.re - R) * Real.log n) := by
  apply norm_dirichletSum_le_real_majorant
  have hd : ‖s - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hs
  have hre : |s.re - c.re| ≤ R := (Complex.abs_re_le_norm (s - c)).trans hd
  linarith [(abs_le.mp hre).1]

end Dubon2026

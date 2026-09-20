import TaoTrudgianYang2025.ZetaCutoffDerivatives
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Quantitative integration by parts for the actual Mellin cutoff

The derivative test functions are constructed from genuine smooth compact
support. Mellin integration by parts retains its factors explicitly,
allowing uniform cutoff derivative masses to control the source kernel.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open RiemannZeta.GuthMaynard
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem support_iteratedDeriv_subset_original (g : ℝ → ℂ) (j : ℕ) :
    Function.support (iteratedDeriv j g) ⊆ tsupport g := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using subset_closure
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact support_deriv_subset.trans (closure_minimal ih isClosed_closure)

def mellinIteratedDerivativeTest {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j : ℕ) :
    DFIVoronoiTestFunction (iteratedDeriv j g) where
  lower := hg.lower
  upper := hg.upper
  lower_pos := hg.lower_pos
  lower_le_upper := hg.lower_le_upper
  smooth := by
    simpa only [iteratedDeriv_eq_iterate] using ContDiff.iterate_deriv j hg.smooth
  support_subset := (support_iteratedDeriv_subset_original g j).trans
    (closure_minimal hg.support_subset isClosed_Icc)

theorem mellinConvergent_complex_of_test {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (s : ℂ) :
    MellinConvergent g s :=
  mellinConvergent_of_isBigO_rpow
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (hg.isBigO_atTop (s.re + 1)) (by simp)
    (hg.isBigO_atZero (s.re - 1)) (by simp)

theorem mellin_derivative_recurrence {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {s : ℂ} (hs : s ≠ 0) : mellin (deriv g) (s + 1) = -s * mellin g s := by
  have hdtest : DFIVoronoiTestFunction (deriv g) := by
    simpa only [iteratedDeriv_one] using mellinIteratedDerivativeTest hg 1
  have hfirst : IntegrableOn (fun x : ℝ => g x * (s * (x : ℂ) ^ (s - 1))) (Ioi 0) := by
    have h := (mellinConvergent_complex_of_test hg s).const_mul s
    simpa only [MellinConvergent, smul_eq_mul, mul_left_comm, mul_comm, mul_assoc] using h
  have hsecond : IntegrableOn (fun x : ℝ => deriv g x * (x : ℂ) ^ s) (Ioi 0) := by
    simpa only [MellinConvergent, add_sub_cancel_right, smul_eq_mul, mul_comm] using
      mellinConvergent_complex_of_test hdtest (s + 1)
  have hzero : Tendsto (fun x : ℝ => g x * (x : ℂ) ^ s) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventuallyEq_zero_atZero] with x hx
    simp only [Pi.zero_apply] at hx
    simp only [hx, zero_mul]
  have hinfty : Tendsto (fun x : ℝ => g x * (x : ℂ) ^ s) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventuallyEq_zero_atTop] with x hx
    simp only [Pi.zero_apply] at hx
    simp only [hx, zero_mul]
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := g) (u' := deriv g) (v := fun x : ℝ => (x : ℂ) ^ s)
    (v' := fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    (fun x _ => (contDiff_infty_iff_deriv.mp hg.smooth).1.differentiableAt.hasDerivAt)
    (fun x hx => hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hs)
    hfirst hsecond hzero hinfty
  have hleft : (∫ x : ℝ in Ioi 0, g x * (s * (x : ℂ) ^ (s - 1))) = s * mellin g s := by
    simp only [mellin, smul_eq_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hright : (∫ x : ℝ in Ioi 0, deriv g x * (x : ℂ) ^ s) = mellin (deriv g) (s + 1) := by
    simp only [mellin, add_sub_cancel_right, smul_eq_mul, mul_comm]
  rw [hleft, hright] at hparts
  linear_combination hparts

theorem mellin_iteratedDeriv_norm {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    ‖mellin (iteratedDeriv j g) (s + j)‖ =
      (∏ m ∈ Finset.range j, ‖s + (m : ℂ)‖) * ‖mellin g s‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hne : s + (j : ℂ) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [add_re, natCast_re, zero_re] at hre
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have harg : s + ((j + 1 : ℕ) : ℂ) = (s + (j : ℂ)) + 1 := by push_cast; ring
      rw [harg, iteratedDeriv_succ, mellin_derivative_recurrence
        (mellinIteratedDerivativeTest hg j) hne, norm_mul, norm_neg, ih,
        Finset.prod_range_succ]
      ring

theorem norm_mellin_le_upper_mass {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖mellin g s‖ ≤ hg.upper ^ (s.re - 1) * ∫ x : ℝ, ‖g x‖ := by
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport
  have hmi := (mellinConvergent_complex_of_test hg s).norm
  have hdom := hgi.norm.const_mul (hg.upper ^ (s.re - 1))
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1) * g x‖ := by
      simpa only [mellin, smul_eq_mul] using
        norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
          (fun x : ℝ => (x : ℂ) ^ (s - 1) * g x)
    _ ≤ ∫ x : ℝ in Ioi 0, hg.upper ^ (s.re - 1) * ‖g x‖ := by
      apply integral_mono_ae (by simpa only [MellinConvergent, smul_eq_mul] using hmi) hdom.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      by_cases hgx : g x = 0
      · simp [hgx]
      · rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hx.le (hg.support_subset hgx).2 (by linarith)) (norm_nonneg _)
    _ ≤ ∫ x : ℝ, hg.upper ^ (s.re - 1) * ‖g x‖ :=
      setIntegral_le_integral hdom (Eventually.of_forall fun x =>
        mul_nonneg (Real.rpow_nonneg (hg.lower_pos.le.trans hg.lower_le_upper) _) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

theorem one_add_abs_le_three_mellin_factor {σ : ℝ} (hσ : 1 / 2 ≤ σ) (u : ℝ) (m : ℕ) :
    1 + |u| ≤ 3 * ‖((σ : ℂ) + (u : ℂ) * I) + (m : ℂ)‖ := by
  have hre := Complex.abs_re_le_norm (((σ : ℂ) + (u : ℂ) * I) + (m : ℂ))
  have him := Complex.abs_im_le_norm (((σ : ℂ) + (u : ℂ) * I) + (m : ℂ))
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
    sub_zero, add_zero, natCast_re, add_im, mul_im, mul_one,
    zero_add, natCast_im, abs_of_nonneg (show 0 ≤ σ + m by linarith)] at hre him
  linarith

theorem mellin_weighted_norm_le_derivative {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) (u : ℝ) (j : ℕ) :
    (1 + |u|) ^ j * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      3 ^ j * ‖mellin (iteratedDeriv j g) (((σ : ℂ) + (u : ℂ) * I) + j)‖ := by
  have hprod := Finset.prod_le_prod
    (s := Finset.range j) (f := fun _ => 1 + |u|)
    (g := fun m : ℕ => 3 * ‖((σ : ℂ) + (u : ℂ) * I) + (m : ℂ)‖)
    (fun _ _ => by positivity) (fun m _ => one_add_abs_le_three_mellin_factor hσ u m)
  simp only [Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib] at hprod
  rw [mellin_iteratedDeriv_norm hg (by simpa using (show 0 < σ by linarith))]
  nlinarith [norm_nonneg (mellin g ((σ : ℂ) + (u : ℂ) * I))]

end TaoTrudgianYang2025

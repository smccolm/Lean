import GafniTao.FordLocalDetectorAssembly
import GafniTao.FordZetaBasicExplicit

/-!
# A uniform lower bound for the shifted detector's right vertical bulk

The right edge lies strictly to the right of `Re s = 1`.  Euler positivity
therefore supplies a reciprocal lower bound for `|zeta|`.  This file keeps
the finite physical endpoints and proves the exact `sech^2` mass estimate
needed to insert that lower bound into Ford's shifted detector.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem ford_riemannZeta_real_le_one_add_inv
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (riemannZeta (sigma : ℂ)).re ≤ 1 + 1 / (sigma - 1) := by
  refine (ford_riemannZeta_real_le_centered hsigma).trans ?_
  have hpow : (3 / 2 : ℝ) ^ (1 - sigma) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hden : 0 < sigma - 1 := sub_pos.mpr hsigma
  gcongr

theorem ford_zeta_right_line_norm_lower
    {sigma v M : ℝ} (hsigma : 1 < sigma)
    (hM : 1 + 1 / (sigma - 1) ≤ M) :
    1 / M ≤ ‖riemannZeta ((sigma : ℂ) + I * v)‖ := by
  have hzetaPos : 0 < (riemannZeta (sigma : ℂ)).re := by
    simpa using (riemannZeta_pos_of_one_lt hsigma).1
  have hMPos : 0 < M :=
    lt_of_lt_of_le (by positivity : 0 < 1 + 1 / (sigma - 1)) hM
  have hzetaM : (riemannZeta (sigma : ℂ)).re ≤ M :=
    (ford_riemannZeta_real_le_one_add_inv hsigma).trans hM
  exact (one_div_le_one_div_of_le hzetaPos hzetaM).trans
    (ford_zeta_basic_reciprocal_lower hsigma)

theorem ford_log_zeta_right_line_lower
    {sigma v M : ℝ} (hsigma : 1 < sigma)
    (hM : 1 + 1 / (sigma - 1) ≤ M) :
    -Real.log M ≤ Real.log ‖riemannZeta ((sigma : ℂ) + I * v)‖ := by
  have hMPos : 0 < M :=
    lt_of_lt_of_le (by positivity : 0 < 1 + 1 / (sigma - 1)) hM
  have hzetaNe : riemannZeta ((sigma : ℂ) + I * v) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simpa using hsigma
  have hnormPos : 0 < ‖riemannZeta ((sigma : ℂ) + I * v)‖ :=
    norm_pos_iff.mpr hzetaNe
  have hlog := Real.strictMonoOn_log.monotoneOn
    (inv_pos.mpr hMPos) hnormPos
    (by simpa [one_div] using
      (ford_zeta_right_line_norm_lower (v := v) hsigma hM))
  simpa [one_div, Real.log_inv] using hlog

theorem intervalIntegral_one_div_cosh_sq (a b : ℝ) :
    (∫ u in a..b, 1 / Real.cosh u ^ 2) = Real.tanh b - Real.tanh a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu => hasDerivAt_tanh_sechSq u)
    ((continuous_const.div
      (Real.continuous_cosh.pow 2)
      (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).intervalIntegrable a b)

theorem intervalIntegral_one_div_cosh_sq_le_two
    {a b : ℝ} :
    (∫ u in a..b, 1 / Real.cosh u ^ 2) ≤ 2 := by
  rw [intervalIntegral_one_div_cosh_sq]
  have hb := Real.tanh_lt_one b
  have ha := Real.neg_one_lt_tanh a
  linarith

theorem continuous_log_norm_riemannZeta_right_affine
    {sigma scale t : ℝ} (hsigma : 1 < sigma) :
    Continuous (fun u : ℝ =>
      Real.log ‖riemannZeta
        ((sigma : ℂ) + I * (t + scale * u : ℝ))‖) := by
  have hfun : (fun u : ℝ =>
      Real.log ‖riemannZeta
        ((sigma : ℂ) + I * (t + scale * u : ℝ))‖) =
      fun u : ℝ => Real.log ‖riemannZeta
        (((sigma : ℂ) + I * t) + (u : ℂ) * ((scale : ℂ) * I))‖ := by
    funext u
    congr 3
    push_cast
    ring
  rw [hfun]
  rw [continuous_iff_continuousAt]
  intro u
  have h1 : ((sigma : ℂ) + I * t) +
      (u : ℂ) * ((scale : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hzeta : riemannZeta (((sigma : ℂ) + I * t) +
      (u : ℂ) * ((scale : ℂ) * I)) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simpa using hsigma
  have hder := hasDerivAt_log_norm_riemannZeta_affine
    (z := (sigma : ℂ) + I * t) (d := (scale : ℂ) * I)
    (x := u) h1 hzeta
  exact hder.continuousAt

theorem fordShiftedDetectorPhysicalVerticalBulk_right_lower
    {eta sigma t yLower yUpper M : ℝ}
    (heta : 0 < eta) (hsigma : 1 < sigma + eta)
    (hM : 1 + 1 / (sigma + eta - 1) ≤ M)
    (hy : yLower ≤ yUpper) :
    -(Real.log M) / (2 * eta) ≤
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (eta : ℂ) yLower yUpper := by
  let a := fordDetectorPhysicalScale eta t yLower
  let b := fordDetectorPhysicalScale eta t yUpper
  have hscale : 0 < 2 * eta / Real.pi := div_pos (mul_pos two_pos heta) Real.pi_pos
  have hab : a ≤ b := by
    dsimp only [a, b, fordDetectorPhysicalScale]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hy t) Real.pi_pos.le)
      (mul_nonneg two_pos.le heta.le)
  let f : ℝ → ℝ := fun u =>
    Real.log ‖riemannZeta
      (fordShiftedDetectorCenter sigma t + (eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I)‖ / Real.cosh u ^ 2
  let g : ℝ → ℝ := fun u => -Real.log M / Real.cosh u ^ 2
  have hcenter (u : ℝ) :
      fordShiftedDetectorCenter sigma t + (eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I =
        ((sigma + eta : ℝ) : ℂ) +
          I * (t + 2 * eta * u / Real.pi) := by
    simp only [fordShiftedDetectorCenter]
    push_cast
    ring
  have hfcont : Continuous f := by
    have htshift : Continuous (fun u : ℝ =>
        Real.log ‖riemannZeta
          (((sigma + eta : ℝ) : ℂ) +
            (t + 2 * eta / Real.pi * u : ℝ) * I)‖) := by
      simpa [mul_comm] using
        (continuous_log_norm_riemannZeta_right_affine
          (sigma := sigma + eta) (scale := 2 * eta / Real.pi)
          (t := t) hsigma)
    have hfeq : f = fun u : ℝ =>
        Real.log ‖riemannZeta
          (((sigma + eta : ℝ) : ℂ) +
            (t + 2 * eta / Real.pi * u : ℝ) * I)‖ /
          Real.cosh u ^ 2 := by
      funext u
      dsimp only [f]
      rw [hcenter]
      congr 4
      push_cast
      ring
    rw [hfeq]
    apply Continuous.div htshift (Real.continuous_cosh.pow 2)
    intro u
    exact pow_ne_zero 2 (Real.cosh_pos u).ne'
  have hgcont : Continuous g := by
    exact continuous_const.div (Real.continuous_cosh.pow 2)
      (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')
  have hfg : ∀ u ∈ Set.Icc a b, g u ≤ f u := by
    intro u _hu
    have hlog := ford_log_zeta_right_line_lower hsigma hM
      (v := t + 2 * eta * u / Real.pi)
    dsimp only [f, g]
    rw [hcenter]
    have hcosh : 0 < Real.cosh u ^ 2 := sq_pos_of_pos (Real.cosh_pos u)
    apply div_le_div_of_nonneg_right _ hcosh.le
    convert hlog using 1
    all_goals push_cast
    all_goals ring
  have hint := intervalIntegral.integral_mono_on hab
    (show IntervalIntegrable g volume a b from hgcont.intervalIntegrable a b)
    (show IntervalIntegrable f volume a b from hfcont.intervalIntegrable a b) hfg
  rw [show fordShiftedDetectorPhysicalVerticalBulk eta sigma t
      (eta : ℂ) yLower yUpper = (1 / (4 * eta)) * ∫ u in a..b, f u by
        rfl]
  have hmass := intervalIntegral_one_div_cosh_sq_le_two (a := a) (b := b)
  have hcoeff : 0 < 1 / (4 * eta) := by positivity
  have hMlogNonneg : 0 ≤ Real.log M := by
    have hMOne : 1 ≤ M := by
      have : 0 < 1 / (sigma + eta - 1) := by positivity
      linarith
    exact Real.log_nonneg hMOne
  have hgint : (∫ u in a..b, g u) =
      -Real.log M * (∫ u in a..b, 1 / Real.cosh u ^ 2) := by
    dsimp only [g]
    simp only [div_eq_mul_inv, one_mul]
    rw [intervalIntegral.integral_const_mul]
  rw [hgint] at hint
  have hlower : -2 * Real.log M ≤ ∫ u in a..b, f u := by
    have hnegmass :
        -Real.log M * 2 ≤
          -Real.log M * (∫ u in a..b, 1 / Real.cosh u ^ 2) := by
      exact mul_le_mul_of_nonpos_left hmass (neg_nonpos.mpr hMlogNonneg)
    linarith
  calc
    -(Real.log M) / (2 * eta) =
        (1 / (4 * eta)) * (-2 * Real.log M) := by field_simp [heta.ne']; ring
    _ ≤ (1 / (4 * eta)) * ∫ u in a..b, f u :=
      mul_le_mul_of_nonneg_left hlower hcoeff.le

#print axioms fordShiftedDetectorPhysicalVerticalBulk_right_lower

end

end GafniTao

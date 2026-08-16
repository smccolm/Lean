import Mathlib.Analysis.Complex.Liouville
import RiemannZeta.GuthMaynard.HughesYoungGammaRatioJets

open Complex Filter MeasureTheory Set Topology
open Metric
open Classical
open scoped ContDiff

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Cauchy bounds for the Hughes--Young pole-cancelling ratio

The pole-cancelling factor is a fixed rational function of the physical
height.  Extending that height to a complex variable and applying Cauchy's
estimate on a disk of radius `t / 2` gives every real-height derivative with
the required inverse-height scale.
-/

noncomputable def hughesYoungPolynomialRatioShiftComplex
    (z : ℂ) (c u : ℝ) : ℂ :=
  let d : ℂ := (c : ℂ) + (u : ℂ) * I
  let p : ℂ := (1 / 2 : ℂ) + z * I
  let m : ℂ := (1 / 2 : ℂ) - z * I
  ((p + d) * (1 - (p + d))) ^ 2 *
      ((m + d) * (1 - (m + d))) ^ 2 /
    ((p * (1 - p) * m * (1 - m)) ^ 2)

theorem hughesYoungPolynomialRatioShiftComplex_ofReal
    (t c u : ℝ) :
    hughesYoungPolynomialRatioShiftComplex (t : ℂ) c u =
      hughesYoungPolynomialRatioShift t c u := by
  unfold hughesYoungPolynomialRatioShiftComplex
    hughesYoungPolynomialRatioShift afePoleNormalization afeCriticalPoint
  dsimp only
  push_cast
  ring

private theorem re_lower_of_mem_closedBall
    {t R : ℝ} {z : ℂ} (hz : z ∈ closedBall (t : ℂ) R) :
    t - R ≤ z.re := by
  have hdist : dist z (t : ℂ) ≤ R := by
    simpa [dist_comm] using hz
  have hre : |z.re - t| ≤ R := by
    calc
      |z.re - t| = |(z - (t : ℂ)).re| := by simp
      _ ≤ ‖z - (t : ℂ)‖ := Complex.abs_re_le_norm _
      _ = dist z (t : ℂ) := by rw [dist_eq]
      _ ≤ R := hdist
  linarith [neg_le_of_abs_le hre]

private theorem norm_le_center_add_radius
    {t R : ℝ} {z : ℂ} (hz : z ∈ closedBall (t : ℂ) R) :
    ‖z‖ ≤ |t| + R := by
  have hdist : dist z (t : ℂ) ≤ R := by
    simpa [dist_comm] using hz
  calc
    ‖z‖ ≤ ‖z - (t : ℂ)‖ + ‖(t : ℂ)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - (t : ℂ)) (t : ℂ)
    _ = dist z (t : ℂ) + |t| := by
      rw [dist_eq, norm_real, Real.norm_eq_abs]
    _ ≤ |t| + R := by linarith

private theorem central_factor_norm_lower
    {t R : ℝ} {z : ℂ} (hRt : R ≤ t)
    (hz : z ∈ closedBall (t : ℂ) R) :
    t - R ≤ ‖(1 / 2 : ℂ) + z * I‖ ∧
    t - R ≤ ‖1 - ((1 / 2 : ℂ) + z * I)‖ ∧
    t - R ≤ ‖(1 / 2 : ℂ) - z * I‖ ∧
    t - R ≤ ‖1 - ((1 / 2 : ℂ) - z * I)‖ := by
  have hre := re_lower_of_mem_closedBall hz
  have hzre : 0 ≤ z.re := by linarith
  have himPlus : (((1 / 2 : ℂ) + z * I).im) = z.re := by simp
  have himPlusComp : (1 - ((1 / 2 : ℂ) + z * I)).im = -z.re := by simp
  have himMinus : (((1 / 2 : ℂ) - z * I).im) = -z.re := by simp
  have himMinusComp : (1 - ((1 / 2 : ℂ) - z * I)).im = z.re := by simp
  constructor
  · have h := Complex.abs_im_le_norm ((1 / 2 : ℂ) + z * I)
    rw [himPlus, abs_of_nonneg hzre] at h
    exact hre.trans h
  constructor
  · have h := Complex.abs_im_le_norm (1 - ((1 / 2 : ℂ) + z * I))
    rw [himPlusComp, abs_neg, abs_of_nonneg hzre] at h
    exact hre.trans h
  constructor
  · have h := Complex.abs_im_le_norm ((1 / 2 : ℂ) - z * I)
    rw [himMinus, abs_neg, abs_of_nonneg hzre] at h
    exact hre.trans h
  · have h := Complex.abs_im_le_norm (1 - ((1 / 2 : ℂ) - z * I))
    rw [himMinusComp, abs_of_nonneg hzre] at h
    exact hre.trans h

theorem diffContOnCl_hughesYoungPolynomialRatioShiftComplex
    {t : ℝ} (ht : 0 < t) (c u : ℝ) :
    DiffContOnCl ℂ (fun z : ℂ =>
      hughesYoungPolynomialRatioShiftComplex z c u)
      (ball (t : ℂ) (t / 2)) := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hz' : z ∈ closedBall (t : ℂ) (t / 2) :=
    closure_ball_subset_closedBall hz
  obtain ⟨hp, hp', hm, hm'⟩ :=
    central_factor_norm_lower (by linarith) hz'
  have hhalf : 0 < t / 2 := by positivity
  have hp0 : (1 / 2 : ℂ) + z * I ≠ 0 := by
    rw [← norm_pos_iff]
    linarith
  have hp0' : 1 - ((1 / 2 : ℂ) + z * I) ≠ 0 := by
    rw [← norm_pos_iff]
    linarith
  have hm0 : (1 / 2 : ℂ) - z * I ≠ 0 := by
    rw [← norm_pos_iff]
    linarith
  have hm0' : 1 - ((1 / 2 : ℂ) - z * I) ≠ 0 := by
    rw [← norm_pos_iff]
    linarith
  have hden :
      ((((1 / 2 : ℂ) + z * I) *
          (1 - ((1 / 2 : ℂ) + z * I)) *
          ((1 / 2 : ℂ) - z * I) *
          (1 - ((1 / 2 : ℂ) - z * I))) ^ 2) ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hp0 hp0') hm0) hm0'
  unfold hughesYoungPolynomialRatioShiftComplex
  dsimp only
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact hden

private theorem norm_real_add_mul_I_le (a : ℝ) (v : ℂ) :
    ‖(a : ℂ) + v * I‖ ≤ |a| + ‖v‖ := by
  calc
    ‖(a : ℂ) + v * I‖ ≤ ‖(a : ℂ)‖ + ‖v * I‖ := norm_add_le _ _
    _ = |a| + ‖v‖ := by
      rw [norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one]

private theorem norm_affine_factor_le_three_mul
    {t a : ℝ} {v : ℂ} (ht : 3 / 2 ≤ t)
    (ha : |a| ≤ 3 / 2) (hv : ‖v‖ ≤ 2 * t) :
    ‖(a : ℂ) + v * I‖ ≤ 3 * t := by
  exact (norm_real_add_mul_I_le a v).trans <| by linarith

private theorem shifted_factor_norm_upper
    {t c u : ℝ} {z : ℂ} (ht : 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ t / 2)
    (hz : z ∈ closedBall (t : ℂ) (t / 2)) :
    ‖((1 / 2 + c : ℝ) : ℂ) + (z + (u : ℂ)) * I‖ ≤ 3 * t ∧
    ‖((1 / 2 - c : ℝ) : ℂ) - (z + (u : ℂ)) * I‖ ≤ 3 * t ∧
    ‖((1 / 2 + c : ℝ) : ℂ) + (-z + (u : ℂ)) * I‖ ≤ 3 * t ∧
    ‖((1 / 2 - c : ℝ) : ℂ) - (-z + (u : ℂ)) * I‖ ≤ 3 * t := by
  have ht0 : 0 ≤ t := by linarith
  have hzNorm := norm_le_center_add_radius hz
  rw [abs_of_nonneg ht0] at hzNorm
  have hzu : ‖z + (u : ℂ)‖ ≤ 2 * t := by
    calc
      ‖z + (u : ℂ)‖ ≤ ‖z‖ + ‖(u : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + |u| := by rw [norm_real, Real.norm_eq_abs]
      _ ≤ 2 * t := by linarith
  have hmzu : ‖-z + (u : ℂ)‖ ≤ 2 * t := by
    calc
      ‖-z + (u : ℂ)‖ ≤ ‖-z‖ + ‖(u : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + |u| := by rw [norm_neg, norm_real, Real.norm_eq_abs]
      _ ≤ 2 * t := by linarith
  have hplus : |1 / 2 + c| ≤ 3 / 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hminus : |1 / 2 - c| ≤ 3 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have ht' : 3 / 2 ≤ t := by linarith
  have hnegzu : ‖-(z + (u : ℂ))‖ ≤ 2 * t := by
    rw [norm_neg]
    exact hzu
  have hnegmzu : ‖-(-z + (u : ℂ))‖ ≤ 2 * t := by
    rw [norm_neg]
    exact hmzu
  constructor
  · exact norm_affine_factor_le_three_mul ht' hplus hzu
  constructor
  · simpa only [sub_eq_add_neg, neg_mul] using
      norm_affine_factor_le_three_mul ht' hminus (v := -(z + (u : ℂ)))
        hnegzu
  constructor
  · exact norm_affine_factor_le_three_mul ht' hplus hmzu
  · simpa only [sub_eq_add_neg, neg_mul] using
      norm_affine_factor_le_three_mul ht' hminus (v := -(-z + (u : ℂ)))
        hnegmzu

/-- Uniform boundary bound for the complex-height pole-cancelling ratio. -/
theorem norm_hughesYoungPolynomialRatioShiftComplex_le_on_closedBall
    {t c u : ℝ} {z : ℂ} (ht : 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ t / 2)
    (hz : z ∈ closedBall (t : ℂ) (t / 2)) :
    ‖hughesYoungPolynomialRatioShiftComplex z c u‖ ≤ 6 ^ (8 : ℕ) := by
  obtain ⟨hsp, hspc, hsm, hsmc⟩ :=
    shifted_factor_norm_upper ht hc0 hc1 hu hz
  obtain ⟨hcp, hcpc, hcm, hcmc⟩ :=
    central_factor_norm_lower (by linarith) hz
  let sp : ℂ := ((1 / 2 + c : ℝ) : ℂ) + (z + (u : ℂ)) * I
  let sm : ℂ := ((1 / 2 + c : ℝ) : ℂ) + (-z + (u : ℂ)) * I
  let cp : ℂ := (1 / 2 : ℂ) + z * I
  let cm : ℂ := (1 / 2 : ℂ) - z * I
  have hnum : ‖(sp * (1 - sp)) ^ 2 * (sm * (1 - sm)) ^ 2‖ ≤
      (3 * t) ^ 8 := by
    simp only [norm_mul, norm_pow]
    change (‖sp‖ * ‖1 - sp‖) ^ 2 * (‖sm‖ * ‖1 - sm‖) ^ 2 ≤ _
    have hsp' : ‖sp‖ ≤ 3 * t := by simpa [sp] using hsp
    have hspc' : ‖1 - sp‖ ≤ 3 * t := by
      convert hspc using 1
      congr 1
      dsimp [sp]
      push_cast
      ring
    have hsm' : ‖sm‖ ≤ 3 * t := by simpa [sm] using hsm
    have hsmc' : ‖1 - sm‖ ≤ 3 * t := by
      convert hsmc using 1
      congr 1
      dsimp [sm]
      push_cast
      ring
    calc
      (‖sp‖ * ‖1 - sp‖) ^ 2 * (‖sm‖ * ‖1 - sm‖) ^ 2 ≤
          ((3 * t) * (3 * t)) ^ 2 * ((3 * t) * (3 * t)) ^ 2 := by
        gcongr
      _ = (3 * t) ^ 8 := by ring
  have hdenLower : (t / 2) ^ 8 ≤
      ‖(cp * (1 - cp) * cm * (1 - cm)) ^ 2‖ := by
    simp only [norm_pow, norm_mul]
    have hcp' : t / 2 ≤ ‖cp‖ := by dsimp [cp]; linarith
    have hcpc' : t / 2 ≤ ‖1 - cp‖ := by dsimp [cp]; linarith
    have hcm' : t / 2 ≤ ‖cm‖ := by dsimp [cm]; linarith
    have hcmc' : t / 2 ≤ ‖1 - cm‖ := by dsimp [cm]; linarith
    calc
      (t / 2) ^ 8 =
          (((t / 2) * (t / 2) * (t / 2) * (t / 2)) ^ 2) := by ring
      _ ≤ (‖cp‖ * ‖1 - cp‖ * ‖cm‖ * ‖1 - cm‖) ^ 2 := by
        gcongr
  have hdenPos : 0 < ‖(cp * (1 - cp) * cm * (1 - cm)) ^ 2‖ :=
    (pow_pos (by positivity : 0 < t / 2) 8).trans_le hdenLower
  unfold hughesYoungPolynomialRatioShiftComplex
  dsimp only
  have heq :
      (((1 / 2 : ℂ) + z * I + ((c : ℂ) + (u : ℂ) * I)) *
          (1 - ((1 / 2 : ℂ) + z * I + ((c : ℂ) + (u : ℂ) * I)))) ^ 2 *
        (((1 / 2 : ℂ) - z * I + ((c : ℂ) + (u : ℂ) * I)) *
          (1 - ((1 / 2 : ℂ) - z * I + ((c : ℂ) + (u : ℂ) * I)))) ^ 2 /
        (((1 / 2 : ℂ) + z * I) * (1 - ((1 / 2 : ℂ) + z * I)) *
          ((1 / 2 : ℂ) - z * I) * (1 - ((1 / 2 : ℂ) - z * I))) ^ 2 =
      (sp * (1 - sp)) ^ 2 * (sm * (1 - sm)) ^ 2 /
        (cp * (1 - cp) * cm * (1 - cm)) ^ 2 := by
    dsimp [sp, sm, cp, cm]
    push_cast
    ring
  rw [heq]
  rw [norm_div, div_le_iff₀ hdenPos]
  calc
    ‖(sp * (1 - sp)) ^ 2 * (sm * (1 - sm)) ^ 2‖ ≤ (3 * t) ^ 8 := hnum
    _ = 6 ^ (8 : ℕ) * (t / 2) ^ 8 := by ring
    _ ≤ 6 ^ (8 : ℕ) * ‖(cp * (1 - cp) * cm * (1 - cm)) ^ 2‖ := by
      gcongr

/-- Iterated differentiation commutes with restricting a holomorphic complex
function to the real axis, as long as the real point stays in an interval on
which the complex function is analytic.  This is the exact bridge needed to
apply the complex Cauchy estimate to a height derivative in Hughes--Young. -/
theorem iteratedDeriv_comp_ofReal_of_analyticAt_Ioi
    (F : ℂ → ℂ)
    (hF : ∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ))
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ => F (y : ℂ)) x =
      iteratedDeriv n F (x : ℂ) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hEq : Set.EqOn
          (iteratedDeriv n (fun y : ℝ => F (y : ℂ)))
          (fun y : ℝ => iteratedDeriv n F (y : ℂ)) (Set.Ioi 0) := by
        intro y hy
        exact ih hy
      have hDerivEq := hEq.deriv isOpen_Ioi hx
      rw [hDerivEq]
      have hAn : AnalyticAt ℂ (iteratedDeriv n F) (x : ℂ) := by
        rw [iteratedDeriv_eq_iterate]
        exact (hF x hx).iterated_deriv n
      exact hAn.differentiableAt.hasDerivAt.comp_ofReal.deriv

private theorem analyticAt_hughesYoungPolynomialRatioShiftComplex_of_pos
    (c u : ℝ) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℂ (fun z : ℂ =>
      hughesYoungPolynomialRatioShiftComplex z c u) (t : ℂ) := by
  have hdiff :=
    diffContOnCl_hughesYoungPolynomialRatioShiftComplex ht c u
  have hdiffOn : DifferentiableOn ℂ (fun z : ℂ =>
      hughesYoungPolynomialRatioShiftComplex z c u)
      (ball (t : ℂ) (t / 2)) :=
    hdiff.differentiableOn
  have hAn := hdiffOn.analyticOnNhd isOpen_ball
  exact hAn (t : ℂ) (mem_ball_self (by positivity))

/-- Cauchy's estimate for every physical-height derivative of the
Hughes--Young pole-cancelling rational factor. -/
theorem norm_iteratedDeriv_hughesYoungPolynomialRatioShift_le_cauchy
    (n : ℕ) {t c u : ℝ} (ht : 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ t / 2) :
    ‖iteratedDeriv n (fun x : ℝ =>
        hughesYoungPolynomialRatioShift x c u) t‖ ≤
      n.factorial * 6 ^ (8 : ℕ) / (t / 2) ^ n := by
  let F : ℂ → ℂ := fun z =>
    hughesYoungPolynomialRatioShiftComplex z c u
  have ht0 : 0 < t := by linarith
  have hR : 0 < t / 2 := by positivity
  have hdiff : DiffContOnCl ℂ F (ball (t : ℂ) (t / 2)) := by
    simpa [F] using
      diffContOnCl_hughesYoungPolynomialRatioShiftComplex ht0 c u
  have hboundary : ∀ z ∈ sphere (t : ℂ) (t / 2), ‖F z‖ ≤ 6 ^ (8 : ℕ) := by
    intro z hz
    apply norm_hughesYoungPolynomialRatioShiftComplex_le_on_closedBall
        ht hc0 hc1 hu
    exact sphere_subset_closedBall hz
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hdiff hboundary
  have hrestrict :
      iteratedDeriv n (fun x : ℝ => F (x : ℂ)) t =
        iteratedDeriv n F (t : ℂ) := by
    apply iteratedDeriv_comp_ofReal_of_analyticAt_Ioi F
    · intro x hx
      simpa [F] using
        analyticAt_hughesYoungPolynomialRatioShiftComplex_of_pos c u hx
    · exact ht0
  rw [← hrestrict] at hcauchy
  simpa only [F, hughesYoungPolynomialRatioShiftComplex_ofReal] using hcauchy

/-- On the Hughes--Young height range, the Cauchy radius gives the same
common inverse-height/shift scale as the paired Gamma quotient. -/
theorem norm_iteratedDeriv_hughesYoungPolynomialRatioShift_le_commonScale
    (n : ℕ) {T t c u : ℝ} (hT : 16 ≤ T) (ht : T / 4 ≤ t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) :
    ‖iteratedDeriv n (fun x : ℝ =>
        hughesYoungPolynomialRatioShift x c u) t‖ ≤
      (n.factorial * 6 ^ (8 : ℕ)) *
        (((T / 16)⁻¹ * (1 + |u|)) ^ n) := by
  have hT0 : 0 < T := by linarith
  have ht4 : 4 ≤ t := by linarith
  have hut : |u| ≤ t / 2 := by linarith
  have hraw := norm_iteratedDeriv_hughesYoungPolynomialRatioShift_le_cauchy
    n ht4 hc0 hc1 hut
  let S : ℝ := (T / 16)⁻¹ * (1 + |u|)
  have hSinv : 2 / t ≤ S := by
    dsimp [S]
    have ht0 : 0 < t := by linarith
    have hbase : 2 / t ≤ 8 / T := by
      apply (div_le_div_iff₀ ht0 hT0).2
      nlinarith
    have h8 : 8 / T ≤ (T / 16)⁻¹ := by
      rw [inv_div]
      exact (div_le_div_iff_of_pos_right hT0).2 (by norm_num)
    have hfactor : (T / 16)⁻¹ ≤ (T / 16)⁻¹ * (1 + |u|) := by
      have hnonneg : 0 ≤ (T / 16)⁻¹ := by positivity
      nlinarith [abs_nonneg u]
    exact hbase.trans (h8.trans hfactor)
  have h2t0 : 0 ≤ 2 / t := by positivity
  have hS0 : 0 ≤ S := h2t0.trans hSinv
  have hpow : (2 / t) ^ n ≤ S ^ n :=
    pow_le_pow_left₀ h2t0 hSinv n
  calc
    ‖iteratedDeriv n (fun x : ℝ =>
        hughesYoungPolynomialRatioShift x c u) t‖ ≤
        n.factorial * 6 ^ (8 : ℕ) / (t / 2) ^ n := hraw
    _ = (n.factorial * 6 ^ (8 : ℕ)) * (2 / t) ^ n := by
      rw [div_eq_mul_inv, ← inv_pow]
      congr 1
      field_simp
    _ ≤ (n.factorial * 6 ^ (8 : ℕ)) * S ^ n := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := rfl

/-- The pole-cancelling rational factor is smooth for every real height: its
four denominator factors have real part `1/2`. -/
theorem contDiff_hughesYoungPolynomialRatioShift (c u : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      hughesYoungPolynomialRatioShift t c u) := by
  have hp (t : ℝ) : (afeCriticalPoint t : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [afeCriticalPoint] at hre
  have hp' (t : ℝ) : (1 - afeCriticalPoint t : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [afeCriticalPoint] at hre
  unfold hughesYoungPolynomialRatioShift afePoleNormalization
  dsimp only
  let s₁ : ℝ → ℂ := fun t =>
    ((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
  let s₂ : ℝ → ℂ := fun t =>
    ((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I
  let p : ℝ → ℂ := fun t => afeCriticalPoint t
  let m : ℝ → ℂ := fun t => afeCriticalPoint (-t)
  have hcast : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have htu : ContDiff ℝ ∞ (fun t : ℝ => ((t + u : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_add] using
      hcast.add (contDiff_const : ContDiff ℝ ∞ (fun _t : ℝ => (u : ℂ)))
  have hmtu : ContDiff ℝ ∞ (fun t : ℝ => ((-t + u : ℝ) : ℂ)) := by
    have hneg : ContDiff ℝ ∞ (fun t : ℝ => ((-t : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_neg
    simpa only [Complex.ofReal_add] using
      hneg.add (contDiff_const : ContDiff ℝ ∞ (fun _t : ℝ => (u : ℂ)))
  have hs₁ : ContDiff ℝ ∞ s₁ := by
    dsimp [s₁]
    exact contDiff_const.add
      (htu.mul contDiff_const)
  have hs₂ : ContDiff ℝ ∞ s₂ := by
    dsimp [s₂]
    exact contDiff_const.add
      (hmtu.mul contDiff_const)
  have hpD : ContDiff ℝ ∞ p := by
    dsimp [p, afeCriticalPoint]
    exact contDiff_const.add (hcast.mul contDiff_const)
  have hmD : ContDiff ℝ ∞ m := by
    dsimp [m, afeCriticalPoint]
    have hneg : ContDiff ℝ ∞ (fun t : ℝ => ((-t : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_neg
    exact contDiff_const.add (hneg.mul contDiff_const)
  have hnum : ContDiff ℝ ∞ (fun t : ℝ =>
      ((↑(1 / 2 + c) + ↑(t + u) * I) *
          (1 - (↑(1 / 2 + c) + ↑(t + u) * I))) ^ 2 *
        ((↑(1 / 2 + c) + ↑(-t + u) * I) *
          (1 - (↑(1 / 2 + c) + ↑(-t + u) * I))) ^ 2) := by
    simpa only [s₁, s₂] using
      ((hs₁.mul (contDiff_const.sub hs₁)).pow 2).mul
        ((hs₂.mul (contDiff_const.sub hs₂)).pow 2)
  have hden : ContDiff ℝ ∞ (fun t : ℝ =>
      (afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) ^ 2) := by
    simpa only [p, m] using
      (((hpD.mul (contDiff_const.sub hpD)).mul hmD).mul
        (contDiff_const.sub hmD)).pow 2
  have hden0 : ∀ t : ℝ,
      (afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) ^ 2 ≠ 0 := by
    intro t
    apply pow_ne_zero
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (hp t) (hp' t)) (hp (-t))) (hp' (-t))
  simpa only [div_eq_mul_inv] using hnum.mul (hden.inv hden0)

end RiemannZeta.GuthMaynard

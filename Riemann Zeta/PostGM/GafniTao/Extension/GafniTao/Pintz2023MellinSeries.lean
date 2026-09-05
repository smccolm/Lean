import GafniTao.Pintz2023MellinKernel
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Pintz (2023), equation (3.5): series/integral interchange

This file moves the literal smoothing kernel through the absolutely
convergent Dirichlet series on `Re w = 2` and identifies the result with the
actual Riemann zeta function.
-/

open Complex Set MeasureTheory Filter
open scoped BigOperators Topology

namespace GafniTao

noncomputable section

theorem pintz2023_div_rpow_neg_two
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a / b) ^ (-(2 : ℝ)) = b ^ 2 * a ^ (-(2 : ℝ)) := by
  rw [Real.div_rpow ha.le hb.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  norm_num [Real.rpow_two]
  field_simp

theorem pintz2023_cpow_div_neg
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℂ) :
    ((a / b : ℝ) : ℂ) ^ (-w) =
      (b : ℂ) ^ w * (a : ℂ) ^ (-w) := by
  have hab : 0 < a / b := div_pos ha hb
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hab.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')]
  rw [← Complex.ofReal_log hab.le, ← Complex.ofReal_log hb.le,
    ← Complex.ofReal_log ha.le, Real.log_div ha.ne' hb.ne', Complex.ofReal_sub]
  have harg :
      ((Real.log a : ℂ) - (Real.log b : ℂ)) * (-w) =
        (Real.log b : ℂ) * w + (Real.log a : ℂ) * (-w) := by ring
  rw [harg, Complex.exp_add]

noncomputable def pintz2023MellinSeriesTerm
    (N : ℕ) (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  if n = 0 then 0 else
    (n : ℂ) ^ (-s) * pintz2023MellinKernelIntegrand N n t

theorem continuous_pintz2023MellinSeriesTerm
    {N n : ℕ} {s : ℂ} (hN : 0 < N) :
    Continuous (pintz2023MellinSeriesTerm N s n) := by
  by_cases hn : n = 0
  · subst n
    simpa [pintz2023MellinSeriesTerm] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hxTwo : 0 < (n : ℝ) / (2 * N) := by positivity
    have hxOne : 0 < (n : ℝ) / N := by positivity
    have hTwo : Continuous (pintz2023MellinExpIntegrand
        ((n : ℝ) / (2 * N))) := by
      unfold pintz2023MellinExpIntegrand
      exact (Continuous.cpow continuous_const (by fun_prop)
        (fun _ => Complex.ofReal_mem_slitPlane.mpr hxTwo)).mul
          continuous_pintz2023_Gamma_two_vertical
    have hOne : Continuous (pintz2023MellinExpIntegrand
        ((n : ℝ) / N)) := by
      unfold pintz2023MellinExpIntegrand
      exact (Continuous.cpow continuous_const (by fun_prop)
        (fun _ => Complex.ofReal_mem_slitPlane.mpr hxOne)).mul
          continuous_pintz2023_Gamma_two_vertical
    unfold pintz2023MellinSeriesTerm pintz2023MellinKernelIntegrand
    simp only [if_neg hn]
    exact continuous_const.mul (hTwo.sub hOne)

theorem norm_pintz2023MellinSeriesTerm_le
    {N n : ℕ} {s : ℂ} (hN : 0 < N) (t : ℝ) :
    ‖pintz2023MellinSeriesTerm N s n t‖ ≤
      (5 * (N : ℝ) ^ 2 * (n : ℝ) ^ (-s.re - 2)) *
        ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  by_cases hn : n = 0
  · subst n
    rw [pintz2023MellinSeriesTerm]
    rw [if_pos rfl, norm_zero, Nat.cast_zero]
    change (0 : ℝ) ≤
      5 * (N : ℝ) ^ 2 * (0 : ℝ) ^ (-s.re - 2) *
        ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖
    have hFive : (0 : ℝ) ≤ 5 := by norm_num
    have hNSq : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
    have hZeroPow :
        (0 : ℝ) ≤ (0 : ℝ) ^ (-s.re - 2) := Real.rpow_nonneg (by norm_num) _
    have hGamma :
        (0 : ℝ) ≤ ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      norm_nonneg _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hFive hNSq) hZeroPow) hGamma
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
    have hxTwo : 0 < (n : ℝ) / (2 * N) := by positivity
    have hxOne : 0 < (n : ℝ) / N := by positivity
    have hpowN : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos hnreal]
      simp
    have hTwo :
        ‖pintz2023MellinExpIntegrand ((n : ℝ) / (2 * N)) t‖ =
          ((n : ℝ) / (2 * N)) ^ (-(2 : ℝ)) *
            ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
      unfold pintz2023MellinExpIntegrand
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxTwo]
      simp
    have hOne :
        ‖pintz2023MellinExpIntegrand ((n : ℝ) / N) t‖ =
          ((n : ℝ) / N) ^ (-(2 : ℝ)) *
            ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
      unfold pintz2023MellinExpIntegrand
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxOne]
      simp
    unfold pintz2023MellinSeriesTerm pintz2023MellinKernelIntegrand
    rw [if_neg hn, norm_mul, hpowN]
    calc
      (n : ℝ) ^ (-s.re) *
          ‖pintz2023MellinExpIntegrand ((n : ℝ) / (2 * N)) t -
            pintz2023MellinExpIntegrand ((n : ℝ) / N) t‖ ≤
        (n : ℝ) ^ (-s.re) *
          (‖pintz2023MellinExpIntegrand ((n : ℝ) / (2 * N)) t‖ +
            ‖pintz2023MellinExpIntegrand ((n : ℝ) / N) t‖) := by
          gcongr
          exact norm_sub_le _ _
      _ = (n : ℝ) ^ (-s.re) *
          ((((2 * N : ℕ) : ℝ) ^ 2 + (N : ℝ) ^ 2) *
            (n : ℝ) ^ (-(2 : ℝ)) *
            ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖) := by
        rw [hTwo, hOne,
          pintz2023_div_rpow_neg_two hnreal (by positivity : (0 : ℝ) < 2 * N),
          pintz2023_div_rpow_neg_two hnreal hNreal]
        push_cast
        ring
      _ = (5 * (N : ℝ) ^ 2 * (n : ℝ) ^ (-s.re - 2)) *
          ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
        rw [show -s.re - 2 = -s.re + (-(2 : ℝ)) by ring,
          Real.rpow_add hnreal]
        push_cast
        ring

theorem integrable_pintz2023MellinSeriesTerm
    {N n : ℕ} {s : ℂ} (hN : 0 < N) :
    Integrable (pintz2023MellinSeriesTerm N s n) := by
  have hMajorant : Integrable (fun t : ℝ =>
      (5 * (N : ℝ) ^ 2 * (n : ℝ) ^ (-s.re - 2)) *
        ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖) :=
    integrable_pintz2023_Gamma_two_vertical.norm.const_mul _
  exact hMajorant.mono'
    (continuous_pintz2023MellinSeriesTerm hN).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_pintz2023MellinSeriesTerm_le hN))

theorem summable_integral_norm_pintz2023MellinSeriesTerm
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 0 ≤ s.re) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖pintz2023MellinSeriesTerm N s n t‖) := by
  let G : ℝ := ∫ t : ℝ,
    ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖
  have hPower : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine ((hPower.mul_left (5 * (N : ℝ) ^ 2 * G)).of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) ?_)
  intro n
  calc
    (∫ t : ℝ, ‖pintz2023MellinSeriesTerm N s n t‖) ≤
        ∫ t : ℝ, (5 * (N : ℝ) ^ 2 * (n : ℝ) ^ (-s.re - 2)) *
          ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
      apply integral_mono (integrable_pintz2023MellinSeriesTerm hN).norm
        (integrable_pintz2023_Gamma_two_vertical.norm.const_mul _)
      intro t
      exact norm_pintz2023MellinSeriesTerm_le hN t
    _ = (5 * (N : ℝ) ^ 2 * G) * (n : ℝ) ^ (-s.re - 2) := by
      rw [integral_const_mul]
      dsimp only [G]
      ring

noncomputable def pintz2023MellinZetaIntegrand
    (N : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  let w : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * I
  (((2 * N : ℕ) : ℂ) ^ w - (N : ℂ) ^ w) *
    Complex.Gamma w * riemannZeta (s + w)

theorem tsum_pintz2023MellinSeriesTerm_eq
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 0 ≤ s.re) (t : ℝ) :
    (∑' n : ℕ, pintz2023MellinSeriesTerm N s n t) =
      pintz2023MellinZetaIntegrand N s t := by
  let w : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * I
  have hw : 1 < (s + w).re := by dsimp only [w]; simp; linarith
  have hsw : s + w ≠ 0 := Complex.ne_zero_of_one_lt_re hw
  rw [pintz2023MellinZetaIntegrand, show
      riemannZeta (s + w) = ∑' n : ℕ, 1 / (n : ℂ) ^ (s + w) from
        zeta_eq_tsum_one_div_nat_cpow hw]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [pintz2023MellinSeriesTerm, w]
    exact Or.inr hsw
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have htwoN : (0 : ℝ) < 2 * N := by positivity
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    unfold pintz2023MellinSeriesTerm pintz2023MellinKernelIntegrand
      pintz2023MellinExpIntegrand
    rw [if_neg hn, pintz2023_cpow_div_neg hnreal htwoN w,
      pintz2023_cpow_div_neg hnreal hNreal w]
    have hcombine :
        (n : ℂ) ^ (-s) * (n : ℂ) ^ (-w) =
          (n : ℂ) ^ (-(s + w)) := by
      rw [← Complex.cpow_add _ _ hnC]
      congr 1
      ring
    have hrecip :
        1 / (n : ℂ) ^ (s + w) = (n : ℂ) ^ (-(s + w)) := by
      rw [one_div, Complex.cpow_neg]
    rw [hrecip, ← hcombine]
    push_cast
    dsimp only [w]
    norm_num
    ring

/-- Equation (3.5) on the unshifted right line, with the source zeta factor. -/
theorem pintz2023SmoothedZetaSum_eq_right_mellin
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 0 ≤ s.re) :
    pintz2023SmoothedZetaSum N s =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ t : ℝ, pintz2023MellinZetaIntegrand N s t := by
  have hinterchange := integral_tsum_of_summable_integral_norm
    (fun n => integrable_pintz2023MellinSeriesTerm hN)
    (summable_integral_norm_pintz2023MellinSeriesTerm hN hs)
  unfold pintz2023SmoothedZetaSum
  rw [show (∑' n : ℕ, pintz2023SmoothedZetaTerm N s n) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∑' n : ℕ, ∫ t : ℝ, pintz2023MellinSeriesTerm N s n t by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [pintz2023SmoothedZetaTerm, pintz2023MellinSeriesTerm]
    · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
      rw [pintz2023SmoothedZetaTerm_eq hnPos,
        pintz2023HalaszKernel_eq_mellin hN hnPos]
      simp_rw [pintz2023MellinSeriesTerm, if_neg hn]
      rw [MeasureTheory.integral_const_mul]
      ring]
  rw [hinterchange]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact tsum_pintz2023MellinSeriesTerm_eq hN hs t

#print axioms pintz2023_cpow_div_neg
#print axioms summable_integral_norm_pintz2023MellinSeriesTerm
#print axioms tsum_pintz2023MellinSeriesTerm_eq
#print axioms pintz2023SmoothedZetaSum_eq_right_mellin

end

end GafniTao

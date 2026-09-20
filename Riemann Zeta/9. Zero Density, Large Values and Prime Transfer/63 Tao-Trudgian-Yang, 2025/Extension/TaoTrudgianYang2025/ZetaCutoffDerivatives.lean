import TaoTrudgianYang2025.ZetaIntervalCutoff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Uniform derivative mass of the exact integer-interval cutoff

All positive-order derivatives are supported in two fixed-width endpoint
pieces. Their integral norms are bounded independently of the interval.
These are quantitative inputs for the actual Mellin source identity.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem zetaIntervalCutoff_eq_transition_sum {a b : ℕ} (hab : a ≤ b) (x : ℝ) :
    zetaIntervalCutoff a b x = Real.smoothTransition (2 * (x - a) + 1) +
      Real.smoothTransition (2 * (b - x) + 1) - 1 := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  unfold zetaIntervalCutoff
  rcases le_total x (a : ℝ) with hx | hx
  · rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * (b - x) + 1)]
    ring
  · rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * (x - a) + 1)]
    ring

theorem iteratedDeriv_smoothTransition_affine (j : ℕ) (c d x : ℝ) :
    iteratedDeriv j (fun y => Real.smoothTransition (c * y + d)) x =
      c ^ j * iteratedDeriv j Real.smoothTransition (c * x + d) := by
  have h : ContDiff ℝ j (fun y => Real.smoothTransition (y + d)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  rw [iteratedDeriv_comp_const_mul h c, iteratedDeriv_comp_add_const]

theorem iteratedDeriv_zetaIntervalCutoff {a b : ℕ} (hab : a ≤ b)
    {j : ℕ} (hj : 0 < j) (x : ℝ) :
    iteratedDeriv j (zetaIntervalCutoff a b) x =
      2 ^ j * iteratedDeriv j Real.smoothTransition (2 * (x - a) + 1) +
        (-2) ^ j * iteratedDeriv j Real.smoothTransition (2 * (b - x) + 1) := by
  have heq : zetaIntervalCutoff a b = fun y =>
      (Real.smoothTransition (2 * y + (1 - 2 * a)) +
        Real.smoothTransition ((-2) * y + (2 * b + 1))) - 1 := by
    funext y
    rw [zetaIntervalCutoff_eq_transition_sum hab]
    congr 2 <;> congr 1 <;> ring
  rw [heq, iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_const, if_neg (Nat.ne_of_gt hj), sub_zero,
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_smoothTransition_affine, iteratedDeriv_smoothTransition_affine]
  congr 2 <;> congr 1 <;> ring

theorem support_iteratedDeriv_smoothTransition {j : ℕ} (hj : 0 < j) :
    Function.support (iteratedDeriv j Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  by_contra h
  have hcases : x < 0 ∨ 1 < x := by simpa only [mem_Icc, not_and_or, not_le] using h
  rcases hcases with hleft | hright
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hleft] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact hx (by rw [heq.iteratedDeriv_eq j, iteratedDeriv_const, if_neg (Nat.ne_of_gt hj)])
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hright] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact hx (by rw [heq.iteratedDeriv_eq j, iteratedDeriv_const, if_neg (Nat.ne_of_gt hj)])

theorem integrable_iteratedDeriv_smoothTransition {j : ℕ} (hj : 0 < j) :
    Integrable (iteratedDeriv j Real.smoothTransition) := by
  have hc : Continuous (iteratedDeriv j Real.smoothTransition) :=
    Real.smoothTransition.contDiff.continuous_iteratedDeriv' j
  have hs : HasCompactSupport (iteratedDeriv j Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx =>
      Function.notMem_support.mp (fun hmem => hx (support_iteratedDeriv_smoothTransition hj hmem)))
  exact hc.integrable_of_hasCompactSupport hs

def zetaCutoffDerivativeMass (j : ℕ) : ℝ :=
  2 ^ j * ∫ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖

theorem zetaCutoffDerivativeMass_nonneg (j : ℕ) : 0 ≤ zetaCutoffDerivativeMass j := by
  unfold zetaCutoffDerivativeMass
  positivity

theorem integrable_iteratedDeriv_zetaIntervalCutoff {a b : ℕ} (hab : a ≤ b)
    {j : ℕ} (hj : 0 < j) : Integrable (iteratedDeriv j (zetaIntervalCutoff a b)) := by
  have h := integrable_iteratedDeriv_smoothTransition hj
  have hleft := ((h.comp_add_right (1 - 2 * a)).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul (2 ^ j)
  have hright := ((h.comp_add_right (2 * b + 1)).comp_mul_left' (by norm_num : (-2 : ℝ) ≠ 0)).const_mul ((-2) ^ j)
  apply (hleft.add hright).congr
  filter_upwards with x
  dsimp only [Pi.add_apply]
  rw [iteratedDeriv_zetaIntervalCutoff hab hj]
  congr 2 <;> congr 1 <;> ring

theorem integral_norm_iteratedDeriv_zetaIntervalCutoff_le {a b : ℕ} (hab : a ≤ b)
    {j : ℕ} (hj : 0 < j) :
    (∫ x : ℝ, ‖iteratedDeriv j (zetaIntervalCutoff a b) x‖) ≤ zetaCutoffDerivativeMass j := by
  have h := (integrable_iteratedDeriv_smoothTransition hj).norm
  have hleft := ((h.comp_add_right (1 - 2 * a)).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul (2 ^ j)
  have hright := ((h.comp_add_right (2 * b + 1)).comp_mul_left' (by norm_num : (-2 : ℝ) ≠ 0)).const_mul (2 ^ j)
  calc
    _ ≤ ∫ x : ℝ, 2 ^ j * ‖iteratedDeriv j Real.smoothTransition (2 * x + (1 - 2 * a))‖ +
        2 ^ j * ‖iteratedDeriv j Real.smoothTransition ((-2) * x + (2 * b + 1))‖ := by
      apply integral_mono (integrable_iteratedDeriv_zetaIntervalCutoff hab hj).norm (hleft.add hright)
      intro x
      dsimp only [Pi.add_apply]
      rw [iteratedDeriv_zetaIntervalCutoff hab hj]
      have htriangle := norm_add_le
        (2 ^ j * iteratedDeriv j Real.smoothTransition (2 * (x - a) + 1))
        ((-2) ^ j * iteratedDeriv j Real.smoothTransition (2 * (b - x) + 1))
      simp only [norm_mul, norm_pow, norm_neg, Real.norm_ofNat] at htriangle
      have hargLeft : 2 * x + (1 - 2 * (a : ℝ)) = 2 * (x - a) + 1 := by ring
      have hargRight : (-2) * x + (2 * (b : ℝ) + 1) = 2 * (b - x) + 1 := by ring
      simpa only [hargLeft, hargRight] using htriangle
    _ = zetaCutoffDerivativeMass j := by
      rw [integral_add hleft hright, integral_const_mul, integral_const_mul,
        Measure.integral_comp_mul_left (fun x => ‖iteratedDeriv j Real.smoothTransition (x + (1 - 2 * a))‖),
        Measure.integral_comp_mul_left (fun x => ‖iteratedDeriv j Real.smoothTransition (x + (2 * b + 1))‖),
        integral_add_right_eq_self (fun x => ‖iteratedDeriv j Real.smoothTransition x‖),
        integral_add_right_eq_self (fun x => ‖iteratedDeriv j Real.smoothTransition x‖)]
      norm_num [zetaCutoffDerivativeMass, smul_eq_mul]
      ring

theorem iteratedDeriv_complex_zetaIntervalCutoff (a b j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y => (zetaIntervalCutoff a b y : ℂ)) x =
      ((iteratedDeriv j (zetaIntervalCutoff a b) x : ℝ) : ℂ) := by
  simpa only [Complex.real_smul, mul_one] using
    iteratedDeriv_smul_const ((contDiff_zetaIntervalCutoff a b).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top j)))).contDiffAt (1 : ℂ)

theorem integral_norm_complex_cutoff_deriv_le {a b : ℕ} (hab : a ≤ b)
    {j : ℕ} (hj : 0 < j) :
    (∫ x : ℝ, ‖iteratedDeriv j (fun y => (zetaIntervalCutoff a b y : ℂ)) x‖) ≤
      zetaCutoffDerivativeMass j := by
  simp_rw [iteratedDeriv_complex_zetaIntervalCutoff, Complex.norm_real]
  exact integral_norm_iteratedDeriv_zetaIntervalCutoff_le hab hj

end TaoTrudgianYang2025

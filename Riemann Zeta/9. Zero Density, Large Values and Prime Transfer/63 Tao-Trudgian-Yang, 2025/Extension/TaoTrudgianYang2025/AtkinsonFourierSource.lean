import TaoTrudgianYang2025.AtkinsonRootFourierDecay

/-!
# Exact Fourier representation of both source carriers

The square-root Jacobian, unit constant phase and signed frequency are
retained. This is an identity for the actual power-weighted divisor source.
-/

noncomputable section

open Complex Set MeasureTheory
open scoped FourierTransform

namespace TaoTrudgianYang2025

theorem atkinsonRootPhase_normalized {T u : ℝ} (hT : 0 < T) (hu : 0 < u) (b : ℝ) :
    2 * Real.pi * atkinsonRootPhase T b (Real.sqrt T * u) =
      T * Real.log T + T * atkinsonRootStationaryProfile u + 4 * Real.pi * b * Real.sqrt T * u := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  unfold atkinsonRootPhase atkinsonRootStationaryProfile
  rw [Real.log_mul hs.ne' hu.ne', Real.log_sqrt hT.le, mul_pow, Real.sq_sqrt hT.le]
  field_simp
  ring

theorem atkinsonRootKernel_normalized {T u : ℝ} (hT : 0 < T) (hu : 0 < u) (b : ℝ) :
    atkinsonRootKernel T b (Real.sqrt T * u) =
      atkinsonPhaseExponential T (Real.log T) *
        atkinsonPhaseExponential T (atkinsonRootStationaryProfile u) *
          Complex.exp (((4 * Real.pi * b * Real.sqrt T * u : ℝ) : ℂ) * I) := by
  have he := congrArg (fun x : ℝ => (x : ℂ) * I) (atkinsonRootPhase_normalized hT hu b)
  unfold atkinsonRootKernel atkinsonPhaseExponential
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast at he ⊢
  linear_combination he

theorem fourier_atkinsonRootFourierAmplitude_eq_interval {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α b : ℝ) :
    𝓕 (atkinsonRootFourierAmplitude T G L α) (-2 * b * Real.sqrt T) =
      ∫ u in (1 / 4 : ℝ)..1, atkinsonRootFourierCore T G L α u *
        Complex.exp (((4 * Real.pi * b * Real.sqrt T * u : ℝ) : ℂ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun u : ℝ => Complex.exp (((-2 * Real.pi * u * (-2 * b * Real.sqrt T) : ℝ) : ℂ) * I) •
      atkinsonRootFourierAmplitude T G L α u) =
      fun u => atkinsonRootFourierAmplitude T G L α u *
        Complex.exp (((4 * Real.pi * b * Real.sqrt T * u : ℝ) : ℂ) * I) := by
    funext u
    rw [smul_eq_mul, show -2 * Real.pi * u * (-2 * b * Real.sqrt T) =
      4 * Real.pi * b * Real.sqrt T * u by ring, mul_comm]
  rw [he, intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  have hrestrict : (∫ u : ℝ, atkinsonRootFourierAmplitude T G L α u *
      Complex.exp (((4 * Real.pi * b * Real.sqrt T * u : ℝ) : ℂ) * I)) =
      ∫ u in Icc (1 / 4 : ℝ) 1, atkinsonRootFourierAmplitude T G L α u *
        Complex.exp (((4 * Real.pi * b * Real.sqrt T * u : ℝ) : ℂ) * I) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz : atkinsonRootFourierAmplitude T G L α u = 0 := by
      by_contra hn
      exact hu (support_atkinsonRootFourierAmplitude hT hG hL hwidth α hn)
    rw [hz, zero_mul]
  rw [hrestrict]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  simp only [atkinsonRootFourierAmplitude, if_pos (show 0 < u by linarith [hu.1])]

theorem atkinsonPowerIntegral_eq_fourier {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α b : ℝ) :
    atkinsonPowerIntegral T G L α b =
      (2 * Real.sqrt T : ℝ) • (atkinsonPhaseExponential T (Real.log T) *
        𝓕 (atkinsonRootFourierAmplitude T G L α) (-2 * b * Real.sqrt T)) := by
  have ha : Real.sqrt T * (1 / 4) = Real.sqrt (T / 16) := by
    rw [Real.sqrt_div hT.le]
    norm_num
    ring
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (fun y => atkinsonPowerWeight T G L α (y ^ 2) * atkinsonRootKernel T b y)
    (a := (1 / 4 : ℝ)) (b := 1) (Real.sqrt T)
  rw [ha, mul_one] at hchange
  rw [atkinsonPowerIntegral_eq_root hT hG hL hwidth α b, ← hchange,
    fourier_atkinsonRootFourierAmplitude_eq_interval hT hG hL hwidth α b,
    ← intervalIntegral.integral_const_mul]
  have he : (∫ u in (1 / 4 : ℝ)..1,
      atkinsonPowerWeight T G L α ((Real.sqrt T * u) ^ 2) *
        atkinsonRootKernel T b (Real.sqrt T * u)) =
      ∫ u in (1 / 4 : ℝ)..1, atkinsonPhaseExponential T (Real.log T) *
        (atkinsonRootFourierCore T G L α u *
          Complex.exp (((4 * Real.pi * b * Real.sqrt T * u : ℝ) : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] at hu
    dsimp only
    rw [mul_pow, Real.sq_sqrt hT.le,
      atkinsonRootKernel_normalized hT (show 0 < u by linarith [hu.1]) b,
      atkinsonRootFourierCore_eq_weight_phase hT.ne']
    ring
  rw [he]
  simp only [real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

end TaoTrudgianYang2025

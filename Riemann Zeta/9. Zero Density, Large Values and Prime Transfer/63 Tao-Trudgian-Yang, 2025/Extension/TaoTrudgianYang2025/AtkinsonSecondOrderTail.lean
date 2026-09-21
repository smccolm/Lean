import TaoTrudgianYang2025.AtkinsonFourierSource

/-!
# Second-order bounds for the actual signed divisor integrals

The frequency-square estimate consumes the exact Fourier source identity.
In particular each signed square-root carrier has a uniform inverse-index
bound. This is a coarse far-tail bound, not stationary main-value evaluation.
-/

noncomputable section

open Complex
open scoped FourierTransform

namespace TaoTrudgianYang2025

theorem exists_sq_mul_norm_atkinsonPowerIntegral_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      b ^ 2 * ‖atkinsonPowerIntegral T G L α b‖ ≤
        C * G * T ^ (-α) * T * Real.sqrt T := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_fourier_atkinsonRootFourierAmplitude_le α
  refine ⟨C / 2, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by linarith
  let F := 𝓕 (atkinsonRootFourierAmplitude T G L α) (-2 * b * Real.sqrt T)
  have hn : ‖atkinsonPowerIntegral T G L α b‖ = 2 * Real.sqrt T * ‖F‖ := by
    rw [atkinsonPowerIntegral_eq_fourier hT0 hG hL0 hwidth α b, norm_smul]
    simp only [norm_mul, (norm_atkinsonPhaseExponential_derivatives T (Real.log T)).1,
      one_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      Real.norm_of_nonneg (Real.sqrt_nonneg T)]
    rfl
  have hx : |-2 * b * Real.sqrt T| ^ 2 = 4 * b ^ 2 * T := by
    rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hT0.le]
    ring
  have hh : 4 * b ^ 2 * T * ‖F‖ ≤ C * G * T ^ (-α) * T ^ 2 := by
    have h := hbound T G L (-2 * b * Real.sqrt T) hT hG hGT hL hwidth
    have hm : |-2 * b * Real.sqrt T| ^ 2 ≤ (1 + |-2 * b * Real.sqrt T|) ^ 2 := by
      nlinarith [abs_nonneg (-2 * b * Real.sqrt T)]
    rw [hx] at hm
    exact (mul_le_mul_of_nonneg_right hm (norm_nonneg F)).trans h
  rw [hn]
  calc
    _ = (1 / (2 * T)) * ((4 * b ^ 2 * T * ‖F‖) * Real.sqrt T) := by field_simp; ring
    _ ≤ (1 / (2 * T)) * ((C * G * T ^ (-α) * T ^ 2) * Real.sqrt T) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _))
        (by positivity)
    _ = _ := by field_simp

theorem exists_norm_atkinsonPowerPair_secondOrder_le (α : ℝ) (cPlus cMinus : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → ∀ n : ℕ, 0 < n →
      ‖cPlus * atkinsonPowerIntegral T G L α (Real.sqrt n) +
        cMinus * atkinsonPowerIntegral T G L α (-Real.sqrt n)‖ ≤
          C * G * T ^ (-α) * T * Real.sqrt T / n := by
  obtain ⟨C, hC, hbound⟩ := exists_sq_mul_norm_atkinsonPowerIntegral_le α
  refine ⟨(1 + ‖cPlus‖ + ‖cMinus‖) * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := hbound T G L (Real.sqrt n) hT hG hGT hL hwidth
  have hm := hbound T G L (-Real.sqrt n) hT hG hGT hL hwidth
  rw [Real.sq_sqrt hn0.le] at hp
  rw [neg_sq, Real.sq_sqrt hn0.le] at hm
  apply (le_div_iff₀ hn0).2
  have hs := norm_add_le (cPlus * atkinsonPowerIntegral T G L α (Real.sqrt n))
    (cMinus * atkinsonPowerIntegral T G L α (-Real.sqrt n))
  simp only [norm_mul] at hs
  have hsum := mul_le_mul_of_nonneg_right hs hn0.le
  have hplus := mul_le_mul_of_nonneg_left hp (norm_nonneg cPlus)
  have hminus := mul_le_mul_of_nonneg_left hm (norm_nonneg cMinus)
  have hrest : 0 ≤ C * G * T ^ (-α) * T * Real.sqrt T := by
    have hT0 : 0 < T := by linarith
    positivity
  nlinarith

end TaoTrudgianYang2025

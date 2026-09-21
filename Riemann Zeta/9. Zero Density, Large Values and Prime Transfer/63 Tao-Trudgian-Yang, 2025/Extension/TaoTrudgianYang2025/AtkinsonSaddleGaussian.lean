import TaoTrudgianYang2025.AtkinsonSaddlePhase

/-!
# The actual quadratic Gaussian at the paired saddles

The two source logarithms have opposite signs, but the actual complex
quadratic transform is even. Its damping is linked to the physical ratio n/T.
-/

noncomputable section

open Complex Set

namespace TaoTrudgianYang2025

theorem zetaGaussianQuadraticIntegral_neg (T : ℝ) {G : ℝ} (hG : G ≠ 0) (v : ℝ) :
    zetaGaussianQuadraticIntegral T G (-v) = zetaGaussianQuadraticIntegral T G v := by
  rw [zetaGaussianQuadraticIntegral_eq T (-v) hG, zetaGaussianQuadraticIntegral_eq T v hG,
    Complex.ofReal_neg, neg_sq]

def atkinsonSaddleGaussian (T G : ℝ) (n : ℕ) : ℂ :=
  zetaGaussianQuadraticIntegral T G
    (2 * Real.arsinh (Real.sqrt (Real.pi * (n : ℝ) / (2 * T))))

theorem zetaGaussianQuadraticIntegral_at_saddle {T : ℝ} (hT : 0 < T) (G : ℝ) (n : ℕ) :
    zetaGaussianQuadraticIntegral T G
      (Real.log (zetaAtkinsonSaddle T (Real.sqrt n)) - Real.log (T / (2 * Real.pi))) =
        atkinsonSaddleGaussian T G n := by
  rw [zetaAtkinsonSaddle_log_argument hT, atkinson_sqrt_frequency_normalized hT n]
  rfl

theorem zetaGaussianQuadraticIntegral_at_neg_saddle {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (n : ℕ) :
    zetaGaussianQuadraticIntegral T G
      (Real.log (zetaAtkinsonSaddle T (-Real.sqrt n)) - Real.log (T / (2 * Real.pi))) =
        atkinsonSaddleGaussian T G n := by
  rw [zetaAtkinsonSaddle_log_argument hT, neg_div, Real.arsinh_neg, mul_neg,
    zetaGaussianQuadraticIntegral_neg T hG, atkinson_sqrt_frequency_normalized hT n]
  rfl

theorem atkinsonSaddleGaussian_eq (T : ℝ) {G : ℝ} (hG : G ≠ 0) (n : ℕ) :
    atkinsonSaddleGaussian T G n =
      ((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.arsinh (Real.sqrt (Real.pi * (n : ℝ) / (2 * T))) : ℂ) ^ 2) /
          zetaGaussianQuadraticCoefficient T G) := by
  rw [atkinsonSaddleGaussian, zetaGaussianQuadraticIntegral_eq T _ hG]
  congr 2
  push_cast
  ring

theorem norm_atkinsonSaddleGaussian_le {T G : ℝ} (hT : 0 < T) (hG : 0 < G)
    (hGT : G ^ 2 ≤ 2 * T) (n : ℕ) :
    ‖atkinsonSaddleGaussian T G n‖ ≤ Real.sqrt Real.pi * G *
      Real.exp (-(G * Real.arsinh (Real.sqrt (Real.pi * (n : ℝ) / (2 * T)))) ^ 2 / 2) := by
  have h := norm_zetaGaussianQuadraticIntegral_le hT hG hGT
    (2 * Real.arsinh (Real.sqrt (Real.pi * (n : ℝ) / (2 * T))))
  convert h using 1
  congr 2
  ring

theorem third_mul_le_arsinh {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 2) : x / 3 ≤ Real.arsinh x := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => Real.arsinh z - z / 3)
      ((Real.sqrt (1 + y ^ 2))⁻¹ - 1 / 3) y :=
    (Real.hasDerivAt_arsinh y).sub ((hasDerivAt_id y).div_const 3)
  have hm : MonotoneOn (fun z : ℝ => Real.arsinh z - z / 3) (Icc 0 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) (by fun_prop)
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    have hs : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hs3 : Real.sqrt (1 + y ^ 2) ≤ 3 :=
      (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hy.1, hy.2]⟩
    have h := one_div_le_one_div_of_le hs hs3
    simpa only [one_div] using sub_nonneg.mpr h
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 2) ⟨hx, hx2⟩ hx
  simp only [Real.arsinh_zero, zero_div, sub_zero] at h
  linarith

theorem norm_atkinsonSaddleGaussian_le_physical {T G : ℝ} (hT : 0 < T) (hG : 0 < G)
    (hGT : G ^ 2 ≤ 2 * T) (n : ℕ) (hn : (n : ℝ) ≤ T) :
    ‖atkinsonSaddleGaussian T G n‖ ≤
      Real.sqrt Real.pi * G * Real.exp (-(G ^ 2 * (n : ℝ)) / (12 * T)) := by
  let x := Real.sqrt (Real.pi * (n : ℝ) / (2 * T))
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < 2 * T)).2
    nlinarith [Real.pi_lt_four, Nat.cast_nonneg (α := ℝ) n]
  have ha := third_mul_le_arsinh hx hx2
  have ha0 : 0 ≤ Real.arsinh x := Real.arsinh_nonneg_iff.mpr hx
  have hxsq : x ^ 2 = Real.pi * (n : ℝ) / (2 * T) := Real.sq_sqrt (by positivity)
  have hsq : (n : ℝ) / (6 * T) ≤ (Real.arsinh x) ^ 2 := by
    have hfirst : x ^ 2 / 9 ≤ (Real.arsinh x) ^ 2 := by nlinarith
    apply le_trans _ hfirst
    rw [hxsq]
    apply (div_le_div_iff₀ (by positivity : 0 < 6 * T) (by norm_num : (0 : ℝ) < 9)).2
    have he := (eq_div_iff (by positivity : 2 * T ≠ 0)).mp hxsq
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [Real.pi_gt_three]
  apply (norm_atkinsonSaddleGaussian_le hT hG hGT n).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg G)
  dsimp [x] at h
  calc
    _ = -(G ^ 2 * (Real.arsinh (Real.sqrt (Real.pi * (n : ℝ) / (2 * T)))) ^ 2) / 2 := by ring
    _ ≤ -(G ^ 2 * ((n : ℝ) / (6 * T))) / 2 := by linarith
    _ = _ := by ring

end TaoTrudgianYang2025

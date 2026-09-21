import TaoTrudgianYang2025.AtkinsonSecondOrderTail

/-!
# A uniform arithmetic majorant for both actual leading carriers

The inverse-index gain combines with the exact quarter-power Bessel
coefficient to give divisor exponent five quarters. Unlike the previous
qualitative summability proof, the constant is independent of T, G and L.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_norm_atkinsonLeadingTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → ∀ n : ℕ,
      ‖atkinsonLeadingTerm T G L n‖ ≤ C * G * T ^ (5 / 4 : ℝ) *
        ‖divisorDirichletTerm (5 / 4) n‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_atkinsonPowerPair_secondOrder_le (1 / 4) neumannLeadingPlus neumannLeadingMinus
  let q : ℝ := Real.sqrt Real.pi / Real.pi
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨2 * Real.pi * q * (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n
  by_cases hn : n = 0
  · simp [hn, atkinsonLeadingTerm, divisorWeight, divisorDirichletTerm, LSeries.term]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hT0 : 0 < T := by linarith
  have hnPow : (n : ℝ) ^ (-(1 / 4 : ℝ)) / n = (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    conv_lhs => rhs; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_sub hn0]
    norm_num
  have hTPow : T ^ (-(1 / 4 : ℝ)) * T * Real.sqrt T = T ^ (5 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    conv_lhs => lhs; rhs; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
    norm_num
  have hpi : ‖(-(2 * Real.pi) : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hqn : ‖(Real.sqrt Real.pi / Real.pi : ℂ)‖ = q := by
    simp [q, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hs : ‖(atkinsonBesselScale (1 / 4) n : ℂ)‖ = atkinsonBesselScale (1 / 4) n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (atkinsonBesselScale_nonneg _ _)]
  have hd := norm_divisorDirichletTerm_real (5 / 4) n
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hd
  rw [atkinsonLeadingTerm, atkinsonLeadingIntegral, norm_mul, norm_mul, norm_mul,
    norm_mul, hpi, hqn, hs, hd]
  calc
    _ ≤ ‖divisorWeight n‖ * (2 * Real.pi) *
        (q * atkinsonBesselScale (1 / 4) n *
          (C * G * T ^ (-(1 / 4 : ℝ)) * T * Real.sqrt T / n)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left
        (hbound T G L hT hG hGT hL hwidth n (Nat.pos_of_ne_zero hn))
      exact mul_nonneg hq.le (atkinsonBesselScale_nonneg _ _)
    _ = (2 * Real.pi * q * (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * C) * G *
        (T ^ (-(1 / 4 : ℝ)) * T * Real.sqrt T) *
          (‖divisorWeight n‖ * ((n : ℝ) ^ (-(1 / 4 : ℝ)) / n)) := by
      unfold atkinsonBesselScale
      norm_num only [show (-2 : ℝ) * (1 / 4) = -(1 / 2) by norm_num]
      ring
    _ = _ := by rw [hnPow, hTPow]

theorem summable_atkinsonLeadingTerm_of_secondOrder {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 1 ≤ L) (hwidth : 8 * L ≤ G) :
    Summable (atkinsonLeadingTerm T G L) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_atkinsonLeadingTerm_le
  exact Summable.of_norm_bounded
    ((summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm.mul_left
      (C * G * T ^ (5 / 4 : ℝ))) (hbound T G L hT hG hGT hL hwidth)

end TaoTrudgianYang2025

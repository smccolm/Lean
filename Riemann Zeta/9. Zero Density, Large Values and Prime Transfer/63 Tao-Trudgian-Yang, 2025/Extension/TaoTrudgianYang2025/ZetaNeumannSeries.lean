import TaoTrudgianYang2025.ZetaNeumannRemainder
import GuthMaynard.DFIEquation24

/-!
# Complete divisor-series replacement of Y0 by its two-term expansion

Convergence of the original branch comes from native Voronoi. The
proved remainder is summed using the ordinary divisor series at 5/4.
The new oscillatory series is obtained by subtracting those two
genuinely convergent series, not by splitting a divergent absolute sum.
-/

noncomputable section

open Complex MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaAtkinsonY0Term (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaAtkinsonY0Integrand T G L n x

def zetaAtkinsonTwoTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaAtkinsonTwoTermIntegrand T G L n x

def zetaNeumannRemainderTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaNeumannRemainderIntegrand T G L n x

def zetaAtkinsonTwoTermSum (T G L : ℝ) : ℂ := ∑' n : ℕ, zetaAtkinsonTwoTerm T G L n

theorem zetaAtkinsonY0Term_eq_native {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (n : ℕ) :
    zetaAtkinsonY0Term T G L n =
      divisorWeight n * dfiVoronoiMinusTransform 1 (mellin (zetaAtkinsonDivisorTest T G L)) n := by
  by_cases hn : n = 0
  · simp [hn, zetaAtkinsonY0Term, divisorWeight]
  have h := (zetaAtkinsonDivisorVoronoiTest hT hG hL).dfiEquation29InitialMinusTransform_eq_bessel
    1 (Nat.pos_of_ne_zero hn)
  change dfiVoronoiMinusTransform 1 (mellin (zetaAtkinsonDivisorTest T G L)) n = _ at h
  rw [h]
  simp only [zetaAtkinsonY0Term, zetaAtkinsonY0Integrand, dfiVoronoiMinusBesselTransform,
    Nat.cast_one, div_one, mul_assoc]

theorem summable_zetaAtkinsonY0Term {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    Summable (zetaAtkinsonY0Term T G L) := by
  have h := (summable_norm_dfiVoronoiDualTerm 1 .minusTerm (zetaAtkinsonDivisorTest T G L)).of_norm
  apply h.congr
  intro n
  exact (zetaAtkinsonY0Term_eq_native hT hG hL n).symm

theorem norm_divisorDirichletTerm_real (s : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (s : ℂ) n‖ = ‖divisorWeight n‖ * (n : ℝ) ^ (-s) := by
  by_cases hn : n = 0
  · simp [hn, divisorDirichletTerm, LSeries.term, divisorWeight]
  simp only [divisorDirichletTerm, LSeries.norm_term_eq, hn, if_false, divisorWeight,
    Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem exists_norm_zetaNeumannRemainderTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ,
        ‖zetaNeumannRemainderTerm T G L n‖ ≤ C * G * ‖divisorDirichletTerm (5 / 4) n‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_integral_zetaNeumannRemainder_le
  refine ⟨2 * Real.pi * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n
  by_cases hn : n = 0
  · simp [hn, zetaNeumannRemainderTerm, divisorWeight, divisorDirichletTerm, LSeries.term]
  have hpi : ‖(-(2 * Real.pi) : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hd := norm_divisorDirichletTerm_real (5 / 4) n
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hd
  rw [zetaNeumannRemainderTerm, norm_mul, norm_mul, hpi, hd]
  calc
    _ ≤ ‖divisorWeight n‖ * (2 * Real.pi) * (C * G * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbound T G L hT hG hGT hL hwidth n (Nat.pos_of_ne_zero hn))
        (by positivity)
    _ = _ := by ring

theorem summable_zetaNeumannRemainderTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (zetaNeumannRemainderTerm T G L) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_zetaNeumannRemainderTerm_le
  exact Summable.of_norm_bounded
    ((summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm.mul_left (C * G))
    (hbound T G L hT hG hGT hL hwidth)

theorem zetaAtkinsonTwoTerm_eq_sub {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (n : ℕ) :
    zetaAtkinsonTwoTerm T G L n =
      zetaAtkinsonY0Term T G L n - zetaNeumannRemainderTerm T G L n := by
  by_cases hn : n = 0
  · simp [hn, zetaAtkinsonTwoTerm, zetaAtkinsonY0Term, zetaNeumannRemainderTerm, divisorWeight]
  unfold zetaAtkinsonTwoTerm zetaAtkinsonY0Term zetaNeumannRemainderTerm
  simp_rw [zetaAtkinsonTwoTermIntegrand_eq_sub]
  rw [integral_sub
    (integrable_zetaAtkinsonY0Integrand hT hG hL hwidth (Nat.pos_of_ne_zero hn)).integrableOn
    (integrable_zetaNeumannRemainderIntegrand hT hG hL hwidth (Nat.pos_of_ne_zero hn)).integrableOn]
  ring

theorem summable_zetaAtkinsonTwoTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (zetaAtkinsonTwoTerm T G L) := by
  have h := (summable_zetaAtkinsonY0Term (T := T) (by linarith) hG hL).sub
    (summable_zetaNeumannRemainderTerm hT hG hGT hL hwidth)
  exact h.congr (fun n => (zetaAtkinsonTwoTerm_eq_sub hT hG hL hwidth n).symm)

theorem zetaAtkinsonBesselMinus_sub_twoTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    zetaAtkinsonBesselMinus T G L - zetaAtkinsonTwoTermSum T G L =
      ∑' n : ℕ, zetaNeumannRemainderTerm T G L n := by
  unfold zetaAtkinsonTwoTermSum
  simp_rw [zetaAtkinsonTwoTerm_eq_sub hT hG hL hwidth]
  rw [(summable_zetaAtkinsonY0Term (T := T) (by linarith) hG hL).tsum_sub
    (summable_zetaNeumannRemainderTerm hT hG hGT hL hwidth)]
  change (∑' n : ℕ, zetaAtkinsonY0Term T G L n) -
    ((∑' n : ℕ, zetaAtkinsonY0Term T G L n) - ∑' n : ℕ, zetaNeumannRemainderTerm T G L n) = _
  ring

theorem exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
        ‖zetaAtkinsonBesselMinus T G L - zetaAtkinsonTwoTermSum T G L‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaNeumannRemainderTerm_le
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm (5 / 4) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C * (1 + S), by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  rw [zetaAtkinsonBesselMinus_sub_twoTerm hT hG hGT hL hwidth]
  have hs := summable_zetaNeumannRemainderTerm hT hG hGT hL hwidth
  have hd := (summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm
  calc
    _ ≤ ∑' n : ℕ, ‖zetaNeumannRemainderTerm T G L n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (C * G) * ‖divisorDirichletTerm (5 / 4) n‖ :=
      hs.norm.tsum_le_tsum (hbound T G L hT hG hGT hL hwidth) (hd.mul_left _)
    _ = C * G * S := tsum_mul_left
    _ ≤ _ := by nlinarith

end TaoTrudgianYang2025

import TaoTrudgianYang2025.ZetaFourthContourShift
import Mathlib.Analysis.PSeries

/-!
# Quantitative bounds for the actual divisor contributions

The coefficient is the ordinary divisor function and the contour mass
cost is exactly a constant times the height to the contour real part.
The coarse summability bound is used only on the right tail line.
-/

noncomputable section

open Complex MeasureTheory
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem integral_norm_zetaFourthTerm_vertical (t c : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖) =
      ((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        ∫ u : ℝ, ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ := by
  simp_rw [norm_zetaFourthTerm_vertical]
  exact integral_const_mul _ _

theorem exists_norm_zetaFourthContribution_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*c ≤ t → ∀ n : ℕ,
      ‖zetaFourthContribution t c n‖ ≤
        K*t^c*((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) := by
  obtain ⟨A,hA,hbound⟩ := exists_integral_norm_zetaFourthKernel_le hc
  let B : ℝ := ‖(1/(2*Real.pi):ℂ)‖
  have hB : 0 < B := by
    apply norm_pos_iff.mpr
    exact one_div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  let K : ℝ := B*A*Real.sqrt (Real.pi/98)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro t ht hct n
  calc
    ‖zetaFourthContribution t c n‖
        ≤ B*(∫ u : ℝ, ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖) := by
      rw [zetaFourthContribution,norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hB.le
    _ = B*(((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        ∫ u : ℝ, ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖) := by
      rw [integral_norm_zetaFourthTerm_vertical]
    _ ≤ B*(((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        (A*t^c*Real.sqrt (Real.pi/98))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hbound t ht hct) (by positivity)) hB.le
    _ = _ := by dsimp [K]; ring

theorem summable_fourth_divisorWeight {c : ℝ} (hc : 3/2 < c) :
    Summable (fun n : ℕ => (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) := by
  have hp : Summable (fun n : ℕ => (n:ℝ)^(1/2-c)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) ?_ hp
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.divisors_zero,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    _ ≤ (n:ℝ)*(n:ℝ)^(-(1/2+c)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n)
        (Real.rpow_nonneg hn0.le _)
    _ = (n:ℝ)^(1+(-(1/2+c))) := by
      rw [Real.rpow_add hn0,Real.rpow_one]
    _ = _ := by congr 1; ring

end TaoTrudgianYang2025

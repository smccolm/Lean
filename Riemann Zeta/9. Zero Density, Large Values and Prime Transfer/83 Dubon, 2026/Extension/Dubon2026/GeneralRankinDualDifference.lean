import Dubon2026.GeneralRankinRieszIdentity
import Dubon2026.GammaDualSharpOptimization

/-! # Sharp actual second differences of the finite general-level dual series -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- Every genuine divisor component has the exact three-fifths normalized second-difference bound from its actual linear coefficient mean. -/
theorem exists_divisorGammaDualSeries_shifted_three_fifths_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) (d : Q.divisors) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 1 ≤ x → 0 < y → y ≤ x → x ^ (3 / 5 : ℝ) ≤ y →
      let h : ℝ := x ^ (3 / 5 : ℝ)
      ‖divisorGammaDualSeries f d (y + 2 * h) - 2 * divisorGammaDualSeries f d (y + h) +
        divisorGammaDualSeries f d y‖ / h ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨B, hB, hb⟩ := exists_divisorRectangularDual_sum_zero_upper f (by omega) d
  have hc0 : (divisorRectangularDualCoefficients f d 0).re = 0 := by
    rw [(divisorRectangularDualCoefficients_positive f d).1, zero_re]
  exact exists_gammaRieszDualSeries_shifted_three_fifths_bound _ hc0
    (divisorRectangularDualCoefficients_positive f d).2.1 hB hb (by exact_mod_cast hk : (2 : ℝ) ≤ k)
    (divisorRankinConductor_pos d)

/-- The finite signed general-level dual series preserves the exact three-fifths difference estimate at both unsmoothing base points. -/
theorem exists_generalRankinGammaDualSeries_shifted_three_fifths_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 1 ≤ x → 0 < y → y ≤ x → x ^ (3 / 5 : ℝ) ≤ y →
      let h : ℝ := x ^ (3 / 5 : ℝ)
      ‖generalRankinGammaDualSeries f (y + 2 * h) - 2 * generalRankinGammaDualSeries f (y + h) +
        generalRankinGammaDualSeries f y‖ / h ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
  choose C hC hb using (fun d : Q.divisors => exists_divisorGammaDualSeries_shifted_three_fifths_bound f hk d)
  let B : ℝ := ∑ d : Q.divisors, ‖divisorRankinAmplitude Q d.val k‖ * C d
  have hB : 0 ≤ B := Finset.sum_nonneg (fun d _ => mul_nonneg (norm_nonneg _) (hC d).le)
  refine ⟨B + 1, by linarith, ?_⟩
  intro x y hx hy hyx hhy
  let h : ℝ := x ^ (3 / 5 : ℝ)
  change ‖generalRankinGammaDualSeries f (y + 2 * h) - 2 * generalRankinGammaDualSeries f (y + h) +
    generalRankinGammaDualSeries f y‖ / h ^ 2 ≤ (B + 1) * x ^ (3 / 5 : ℝ)
  have he : generalRankinGammaDualSeries f (y + 2 * h) - 2 * generalRankinGammaDualSeries f (y + h) +
      generalRankinGammaDualSeries f y = ∑ d : Q.divisors, divisorRankinAmplitude Q d.val k *
        (divisorGammaDualSeries f d (y + 2 * h) - 2 * divisorGammaDualSeries f d (y + h) + divisorGammaDualSeries f d y) := by
    simp only [generalRankinGammaDualSeries, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he]
  calc
    _ ≤ (∑ d : Q.divisors, ‖divisorRankinAmplitude Q d.val k *
        (divisorGammaDualSeries f d (y + 2 * h) - 2 * divisorGammaDualSeries f d (y + h) + divisorGammaDualSeries f d y)‖) / h ^ 2 :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (sq_nonneg h)
    _ = ∑ d : Q.divisors, ‖divisorRankinAmplitude Q d.val k‖ *
        (‖divisorGammaDualSeries f d (y + 2 * h) - 2 * divisorGammaDualSeries f d (y + h) + divisorGammaDualSeries f d y‖ / h ^ 2) := by
      rw [Finset.sum_div]
      simp only [norm_mul, mul_div_assoc]
    _ ≤ ∑ d : Q.divisors, ‖divisorRankinAmplitude Q d.val k‖ * (C d * x ^ (3 / 5 : ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left (hb d x y hx hy hyx hhy) (norm_nonneg _)
    _ = B * x ^ (3 / 5 : ℝ) := by
      dsimp [B]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith : 0 ≤ x) _)

end
end Dubon2026

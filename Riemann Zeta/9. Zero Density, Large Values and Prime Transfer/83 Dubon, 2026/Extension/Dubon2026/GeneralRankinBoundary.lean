import Dubon2026.GeneralRankinReflection
import Dubon2026.RankinConvolutionBoundary

/-! # Genuine reflected boundary growth at every positive level -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- Every actual divisor component is uniformly bounded in each closed convergence half-plane. -/
theorem exists_divisorRectangularDual_LSeries_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (d : Q.divisors)
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, σ ≤ s.re → ‖LSeries (divisorRectangularDualCoefficients f d) s‖ ≤ B := by
  have hsum := (divisorRectangularDual_lseriesSummable f hk d (s := (σ : ℂ)) hσ).norm
  let B : ℝ := ∑' n, ‖LSeries.term (divisorRectangularDualCoefficients f d) (σ : ℂ) n‖
  have hB : 0 ≤ B := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨B + 1, by linarith, ?_⟩
  intro s hs
  exact (tsum_of_norm_bounded hsum.hasSum
    (fun n => LSeries.norm_term_le_of_re_le_re _ (s := (σ : ℂ)) hs n)).trans (by linarith)

/-- The genuine finite reflected Riesz series has sharp inverse-square-root decay on its left contour line at every level. -/
theorem exists_general_rankinConvolution_riesz_left_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = -1 / 8 → 1 ≤ |s.im| →
      ‖rankinConvolutionGlobalContinuation f s / (s * (s + 1) * (s + 2))‖ ≤
        C * |s.im| ^ (-(1 / 2 : ℝ)) := by
  choose B hB hBb using (fun d : Q.divisors => exists_divisorRectangularDual_LSeries_bound f
    (by omega : 0 < k) d (show (1 : ℝ) < 9 / 8 by norm_num))
  let C : ℝ := ∑ d : Q.divisors, ‖divisorRankinAmplitude Q d.val k‖ *
    (divisorRankinConductor Q d.val) ^ (-(1 / 8 : ℝ)) * gammaRieszStripConstant k * B d
  have hG : 0 < gammaRieszStripConstant k := Real.exp_pos _
  have hC : 0 ≤ C := Finset.sum_nonneg (fun d _ => by
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (divisorRankinConductor_pos d).le _)) hG.le) (hB d).le)
  refine ⟨C + 1, by linarith, ?_⟩
  intro s hs ht
  rw [general_rankinConvolution_riesz_reflection f (by omega) (by rw [hs]; norm_num) (by rw [hs]; norm_num)]
  calc
    _ ≤ ∑ d : Q.divisors, ‖divisorRankinAmplitude Q d.val k *
        (divisorRankinConductor Q d.val : ℂ) ^ s * gammaRieszSymbol (k : ℝ) 2 s *
          LSeries (divisorRectangularDualCoefficients f d) (1 - s)‖ := norm_sum_le _ _
    _ ≤ ∑ d : Q.divisors, (‖divisorRankinAmplitude Q d.val k‖ *
        (divisorRankinConductor Q d.val) ^ (-(1 / 8 : ℝ)) * gammaRieszStripConstant k * B d) *
          |s.im| ^ (-(1 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      have hp : ‖(divisorRankinConductor Q d.val : ℂ) ^ s‖ =
          (divisorRankinConductor Q d.val) ^ (-(1 / 8 : ℝ)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (divisorRankinConductor_pos d), hs, neg_div]
      have hg := norm_gammaRieszSymbol_two_left_le (k := (k : ℝ)) (by exact_mod_cast hk) hs ht
      have hb := hBb d (1 - s) (by simp only [sub_re, one_re, hs]; norm_num)
      have hw : 0 ≤ ‖divisorRankinAmplitude Q d.val k‖ *
          (divisorRankinConductor Q d.val) ^ (-(1 / 8 : ℝ)) :=
        mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (divisorRankinConductor_pos d).le _)
      simp only [norm_mul, hp]
      calc
        _ ≤ ‖divisorRankinAmplitude Q d.val k‖ *
            (divisorRankinConductor Q d.val) ^ (-(1 / 8 : ℝ)) *
              (gammaRieszStripConstant k * |s.im| ^ (-(1 / 2 : ℝ))) * B d :=
          mul_le_mul (mul_le_mul_of_nonneg_left hg hw) hb (norm_nonneg _)
            (mul_nonneg hw (mul_nonneg hG.le (Real.rpow_nonneg (abs_nonneg _) _)))
        _ = _ := by ring
    _ = C * |s.im| ^ (-(1 / 2 : ℝ)) := by rw [← Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (abs_nonneg _) _)

/-- The actual entire Rankin pole numerator has seven-halves reflected-boundary growth at every positive level. -/
theorem exists_general_rankinConvolutionEntireNumerator_left_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = -1 / 8 → 1 ≤ |s.im| →
      ‖rankinConvolutionEntireNumerator f s‖ ≤ C * |s.im| ^ (7 / 2 : ℝ) := by
  obtain ⟨C, hC, hCb⟩ := exists_general_rankinConvolution_riesz_left_bound f hk
  refine ⟨81 * C, by positivity, ?_⟩
  intro s hs ht
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hp1 : s + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [hs] at hh
  have hp2 : s + 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [hs] at hh
  have he : rankinConvolutionEntireNumerator f s =
      ((s - 1) * (s * (s + 1) * (s + 2))) *
        (rankinConvolutionGlobalContinuation f s / (s * (s + 1) * (s + 2))) := by
    rw [rankinConvolutionGlobalContinuation]
    field_simp [hs0, sub_ne_zero.mpr hs1, hp1, hp2]
  rw [he, norm_mul]
  calc
    _ ≤ (81 * |s.im| ^ 4) * (C * |s.im| ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul (norm_rankin_left_factors_le hs ht) (hCb s hs ht) (norm_nonneg _) (by positivity)
    _ = (81 * C) * (|s.im| ^ (4 : ℝ) * |s.im| ^ (-(1 / 2 : ℝ))) := by
      norm_num only [Real.rpow_ofNat]
      ring
    _ = _ := by rw [← Real.rpow_add (by linarith : 0 < |s.im|)]; norm_num

end
end Dubon2026

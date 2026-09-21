import TaoTrudgianYang2025.ZetaFourthContributionBounds

/-!
# Exact mixed-line truncation of the actual fourth-moment source

The finite prefix is moved to any positive line. The complementary
convergent tail can independently use a farther right line. Its bound
retains the ordinary divisor-weight tail rather than assuming it small.
-/

noncomputable section

open Complex MeasureTheory
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaFourthPrefix (t c : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ n ∈ S, zetaFourthContribution t c n

def zetaFourthTail (t c : ℝ) (S : Finset ℕ) : ℂ :=
  ∑' n : {n : ℕ // n ∉ S}, zetaFourthContribution t c n

theorem zetaFourthPrefix_eq_integral {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (S : Finset ℕ) :
    zetaFourthPrefix t c S = (1/(2*Real.pi):ℂ) *
      ∫ u : ℝ, (∑ n ∈ S,
        divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n) *
          zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I) := by
  unfold zetaFourthPrefix zetaFourthContribution
  rw [← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum S (fun n _ => integrable_zetaFourthTerm_vertical ht hc n)]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [zetaFourthTerm,Finset.sum_mul]

theorem zetaFourthPrefix_line_eq {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaFourthPrefix t a S = zetaFourthPrefix t b S := by
  apply Finset.sum_congr rfl
  intro n _
  exact zetaFourthContribution_line_eq ha hb ht n

theorem zetaFourthRightPiece_eq_prefix_add_tail {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaFourthRightPiece t = zetaFourthPrefix t a S + zetaFourthTail t b S := by
  rw [zetaFourthPrefix_line_eq ht ha hb S,zetaFourthPrefix,zetaFourthTail,
    (hasSum_zetaFourthContribution ht hb).summable.sum_add_tsum_subtype_compl S,
    (hasSum_zetaFourthContribution ht hb).tsum_eq]

theorem summable_norm_zetaFourthTail {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (S : Finset ℕ) :
    Summable (fun n : {n : ℕ // n ∉ S} => ‖zetaFourthContribution t c n‖) :=
  ((hasSum_zetaFourthContribution ht hc).summable.subtype _).norm

theorem exists_norm_zetaFourthTail_le {c : ℝ} (hc : 3/2 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*c ≤ t → ∀ S : Finset ℕ,
      ‖zetaFourthTail t c S‖ ≤ K*t^c*
        ∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+c)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthContribution_le hc0
  refine ⟨K,hK,?_⟩
  intro t ht hct S
  have ht0 : 0 ≤ t := by linarith
  have hs := (summable_fourth_divisorWeight hc).subtype (fun n => n ∉ S)
  calc
    ‖zetaFourthTail t c S‖ ≤
        ∑' n : {n : ℕ // n ∉ S}, ‖zetaFourthContribution t c n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_zetaFourthTail ht0 hc0 S)
    _ ≤ ∑' n : {n : ℕ // n ∉ S},
        K*t^c*(((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+c))) :=
      Summable.tsum_le_tsum (fun n => hbound t ht hct n)
        (summable_norm_zetaFourthTail ht0 hc0 S) (hs.mul_left (K*t^c))
    _ = _ := tsum_mul_left

theorem exists_norm_fourthRightPiece_sub_prefix_le {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ a : ℝ, 0 < a → ∀ S : Finset ℕ,
      ‖zetaFourthRightPiece t - zetaFourthPrefix t a S‖ ≤ K*t^b*
        ∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b)) := by
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthTail_le hb
  refine ⟨K,hK,?_⟩
  intro t ht hbt a ha S
  rw [zetaFourthRightPiece_eq_prefix_add_tail (by linarith : 0 ≤ t)
    ha (by linarith : 0 < b) S,add_sub_cancel_left]
  exact hbound t ht hbt S

theorem zeta_fourth_le_prefix_add_tail {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaMomentCriticalNorm t^4 ≤
      8*‖zetaFourthPrefix t a S‖^2 + 8*‖zetaFourthTail t b S‖^2 := by
  have hz := zeta_fourth_le_four_mul_rightPiece_sq t
  rw [zetaFourthRightPiece_eq_prefix_add_tail ht ha hb S] at hz
  have hnorm := norm_add_le (zetaFourthPrefix t a S) (zetaFourthTail t b S)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_nonneg (‖zetaFourthPrefix t a S‖-‖zetaFourthTail t b S‖)]

theorem exists_zeta_fourth_le_prefix_add_weightTail {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ a : ℝ, 0 < a → ∀ S : Finset ℕ,
      zetaMomentCriticalNorm t^4 ≤ 8*‖zetaFourthPrefix t a S‖^2 +
        8*(K*t^b*(∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b))))^2 := by
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthTail_le hb
  refine ⟨K,hK,?_⟩
  intro t ht hbt a ha S
  have h := zeta_fourth_le_prefix_add_tail (by linarith : 0 ≤ t)
    ha (by linarith : 0 < b) S
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hbound t ht hbt S) 2
  linarith

end TaoTrudgianYang2025

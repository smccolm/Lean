import TaoTrudgianYang2025.FiniteRandomCoefficients

/-! Actual bounded coefficients from finite block vectors and their variance. -/

open Finset

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_bounded_sign_coefficients_of_variance {ι : Type*}
    (I : Finset ℕ) (v : List (ℕ → ℂ)) (W : Finset ι) (w : ι → ℕ → ℂ)
    (S : ℝ) (hS : 0 < S)
    (hunit : ∀ n, (v.map (fun b => ‖b n‖)).sum ≤ 1)
    (hvar : ∀ t ∈ W, S ≤
      (v.map (fun b => Complex.normSq (∑ n ∈ I, b n*w t n))).sum) :
    ∃ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ 1) ∧
      (W.card:ℝ) ≤ 12*({t ∈ W |
        S/2 ≤ Complex.normSq (∑ n ∈ I, a n*w t n)}.card:ℝ) := by
  classical
  have hpos (t : ι) (ht : t ∈ W) :
      0 < (v.map (fun b => Complex.normSq
        (finiteCoefficientEvaluation I (w t) b))).sum :=
    hS.trans_le (hvar t ht)
  obtain ⟨a,ha,hcount⟩ := finiteSignSamples_exists_many_large v W
    (fun t => finiteCoefficientEvaluation I (w t)) hpos
  refine ⟨a,fun n => (finiteSignSamples_apply_norm_le v ha n).trans (hunit n),?_⟩
  apply hcount.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 12)
  exact_mod_cast (show
    ({t ∈ W | (v.map (fun b => Complex.normSq
        (finiteCoefficientEvaluation I (w t) b))).sum/2 ≤
      Complex.normSq (finiteCoefficientEvaluation I (w t) a)}).card ≤
    ({t ∈ W | S/2 ≤ Complex.normSq (∑ n ∈ I, a n*w t n)}).card from
    card_le_card (by
      intro t ht
      have hp := mem_filter.mp ht
      exact mem_filter.mpr ⟨hp.1,
        (div_le_div_of_nonneg_right (hvar t hp.1) (by norm_num)).trans hp.2⟩))

end TaoTrudgianYang2025


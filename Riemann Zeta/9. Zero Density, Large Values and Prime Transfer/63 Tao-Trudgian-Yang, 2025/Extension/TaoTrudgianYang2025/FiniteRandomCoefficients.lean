import TaoTrudgianYang2025.FiniteSignSelection
import TaoTrudgianYang2025.FiniteSignCoefficients
import Mathlib.Data.Finset.Sort

/-! A genuine bounded coefficient choice for arbitrary finite unit-weight evaluations. -/

open Finset

noncomputable section

namespace TaoTrudgianYang2025

def finiteCoefficientBasis (I : Finset ℕ) : List (ℕ → ℂ) :=
  I.toList.map (fun n m => if m = n then (1:ℂ) else 0)

def finiteCoefficientEvaluation (I : Finset ℕ) (w : ℕ → ℂ) : (ℕ → ℂ) →+ ℂ :=
  { toFun := fun a => ∑ n ∈ I, a n*w n
    map_zero' := by simp
    map_add' := by intros; simp [add_mul,sum_add_distrib] }

theorem finiteCoefficientEvaluation_basis (I : Finset ℕ) (w : ℕ → ℂ)
    {n : ℕ} (hn : n ∈ I) :
    finiteCoefficientEvaluation I w (fun m => if m = n then 1 else 0) = w n := by
  simp [finiteCoefficientEvaluation,hn]

theorem finiteCoefficientBasis_norm_sum (I : Finset ℕ) (n : ℕ) :
    ((finiteCoefficientBasis I).map (fun a => ‖a n‖)).sum ≤ 1 := by
  classical
  simp only [finiteCoefficientBasis,List.map_map,Function.comp_def]
  simp only [apply_ite,norm_one,norm_zero]
  rw [Finset.sum_map_toList]
  by_cases hn : n ∈ I
  · simp [hn]
  · simp [hn]

theorem finiteCoefficientBasis_variance (I : Finset ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ I, Complex.normSq (w n) = 1) :
    ((finiteCoefficientBasis I).map
      (fun a => Complex.normSq (finiteCoefficientEvaluation I w a))).sum = (I.card:ℝ) := by
  classical
  simp only [finiteCoefficientBasis,List.map_map,Function.comp_def]
  rw [Finset.sum_map_toList]
  calc
    _ = ∑ _n ∈ I, (1:ℝ) := by
      apply sum_congr rfl
      intro n hn
      rw [finiteCoefficientEvaluation_basis I w hn,hw n hn]
    _ = _ := by simp

theorem exists_bounded_coefficients_many_large {ι : Type*}
    (I : Finset ℕ) (hI : I.Nonempty) (W : Finset ι) (w : ι → ℕ → ℂ)
    (hw : ∀ t ∈ W, ∀ n ∈ I, Complex.normSq (w t n) = 1) :
    ∃ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ 1) ∧
      (W.card:ℝ) ≤ 12*({t ∈ W |
        (I.card:ℝ)/2 ≤ Complex.normSq (∑ n ∈ I, a n*w t n)}.card:ℝ) := by
  classical
  have hvariance (t : ι) (ht : t ∈ W) :=
    finiteCoefficientBasis_variance I (w t) (hw t ht)
  have hpositive (t : ι) (ht : t ∈ W) :
      0 < ((finiteCoefficientBasis I).map
        (fun a => Complex.normSq (finiteCoefficientEvaluation I (w t) a))).sum := by
    rw [hvariance t ht]
    exact_mod_cast hI.card_pos
  obtain ⟨a,ha,hcount⟩ := finiteSignSamples_exists_many_large (finiteCoefficientBasis I)
    W (fun t => finiteCoefficientEvaluation I (w t)) hpositive
  refine ⟨a,fun n => (finiteSignSamples_apply_norm_le _ ha n).trans
    (finiteCoefficientBasis_norm_sum I n),?_⟩
  have heq : {t ∈ W | ((finiteCoefficientBasis I).map
      (fun b => Complex.normSq (finiteCoefficientEvaluation I (w t) b))).sum/2 ≤
        Complex.normSq (finiteCoefficientEvaluation I (w t) a)} =
      {t ∈ W | (I.card:ℝ)/2 ≤ Complex.normSq (∑ n ∈ I, a n*w t n)} := by
    ext t
    simp only [mem_filter]
    constructor
    · rintro ⟨ht,h⟩
      rw [hvariance t ht] at h
      exact ⟨ht,h⟩
    · rintro ⟨ht,h⟩
      refine ⟨ht,?_⟩
      rw [hvariance t ht]
      exact h
  rw [heq] at hcount
  exact hcount

end TaoTrudgianYang2025

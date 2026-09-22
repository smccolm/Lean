import TaoTrudgianYang2025.BetaSmoothCutoff

/-!
# Uniform finite-order bounds for cutoff corrections

Leibniz's formula is bounded using fixed compact maxima of the actual
cutoff derivatives. The resulting bound is independent of the function
being localized and of its error tolerance.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

def cutoffOrderBudget (χ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * |iteratedDeriv i χ x|

def cutoffFiniteBudget (χ : ℝ → ℝ) (Q : ℕ) (x : ℝ) : ℝ :=
  1 + ∑ n ∈ Finset.range (Q+1), cutoffOrderBudget χ n x

theorem cutoffOrderBudget_nonneg (χ : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ cutoffOrderBudget χ n x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

theorem cutoffOrderBudget_le_finite (χ : ℝ → ℝ) {n Q : ℕ}
    (hn : n ≤ Q) (x : ℝ) :
    cutoffOrderBudget χ n x ≤ cutoffFiniteBudget χ Q x := by
  have h := Finset.single_le_sum (s := Finset.range (Q+1))
    (fun k _ => cutoffOrderBudget_nonneg χ k x)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn))
  unfold cutoffFiniteBudget
  linarith

theorem cutoffFiniteBudget_continuous {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (Q : ℕ) : Continuous (cutoffFiniteBudget χ Q) := by
  have hd : ∀ n : ℕ, Continuous (iteratedDeriv n χ) := fun n =>
    hχ.continuous_iteratedDeriv n
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  exact continuous_const.add (continuous_finsetSum _ fun n _ =>
    continuous_finsetSum _ fun i _ => continuous_const.mul (hd i).abs)

theorem smoothCutoff_mul_iteratedDeriv_le {χ H : ℝ → ℝ}
    {x ε : ℝ} (n : ℕ)
    (hχ : ContDiffAt ℝ n χ x) (hH : ContDiffAt ℝ n H x)
    (he : ∀ j ≤ n, |iteratedDeriv j H x| ≤ ε) :
    |iteratedDeriv n (fun y => χ y * H y) x| ≤ cutoffOrderBudget χ n x * ε := by
  rw [iteratedDeriv_fun_mul hχ hH]
  calc
    |∑ i ∈ Finset.range (n+1),
        (n.choose i : ℝ) * iteratedDeriv i χ x * iteratedDeriv (n-i) H x| ≤
      ∑ i ∈ Finset.range (n+1),
        |(n.choose i : ℝ) * iteratedDeriv i χ x * iteratedDeriv (n-i) H x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n+1),
        ((n.choose i : ℝ) * |iteratedDeriv i χ x|) * ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (he (n-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    _ = cutoffOrderBudget χ n x * ε := by rw [cutoffOrderBudget, Finset.sum_mul]

theorem smoothCutoff_uniform_derivative_bound {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {S : Set ℝ} (hS : IsCompact S)
    (hs : tsupport χ ⊆ S) (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℝ) (ε : ℝ), 0 ≤ ε →
      (∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ H x) →
      (∀ x ∈ tsupport χ, ∀ j ≤ Q, |iteratedDeriv j H x| ≤ ε) →
      ∀ x : ℝ, ∀ n ≤ Q, |iteratedDeriv n (fun y => χ y*H y) x| ≤ C*ε := by
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn
    (cutoffFiniteBudget_continuous hχ Q).continuousOn
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro H ε hε hH he x n hn
  by_cases hx : x ∈ tsupport χ
  · have hN : (n : WithTop ℕ∞) ≤ ∞ :=
      ENat.natCast_le_of_coe_top_le_withTop le_rfl n
    have hb : cutoffOrderBudget χ n x ≤ max K 1 :=
      (cutoffOrderBudget_le_finite χ hn x).trans
        ((le_abs_self _).trans ((hK x (hs hx)).trans (le_max_left _ _)))
    exact (smoothCutoff_mul_iteratedDeriv_le n
      (hχ.contDiffAt.of_le hN) ((hH x hx).of_le hN)
      (fun j hj => he x hx j (hj.trans hn))).trans
        (mul_le_mul_of_nonneg_right hb hε)
  · rw [smoothCutoff_mul_iteratedDeriv_zero hx n,abs_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hε

end TaoTrudgianYang2025

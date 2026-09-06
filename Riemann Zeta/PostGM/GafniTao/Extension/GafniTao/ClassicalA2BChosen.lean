import GafniTao.ClassicalA2BScale
import GafniTao.HeathBrownEPHalfLow

/-!
# The selected finite `A²B` estimate on Pintz's source block

This module inserts the two rounded optimal shifts into the exact finite
A²B theorem.  The long-block hypothesis is explicit; its complementary
short-block case is handled by cardinality in the optimizer.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard
open scoped BigOperators

noncomputable section

theorem pintz2023ExponentialBlock_eq_integerLogarithmicPrefix
    {N R : ℕ} (hN : 0 < N) (hNR : N ≤ R) (t : ℝ) :
    pintz2023ExponentialBlock N R t =
      ∑ n ∈ Finset.Ico (0 : ℤ) ((R - N : ℕ) : ℤ),
        integerLogarithmicTerm t (N + 1 : ℕ) n := by
  have hendpoint : N + (R - N) = R := Nat.add_sub_of_le hNR
  calc
    pintz2023ExponentialBlock N R t =
        fordShiftedExponentialSum N R 0 t :=
      pintz2023ExponentialBlock_eq_fordShiftedExponentialSum t hN
    _ = fordShiftedExponentialSum N (N + (R - N)) 0 t := by rw [hendpoint]
    _ = ∑ n ∈ Finset.Ico (0 : ℤ) ((R - N : ℕ) : ℤ),
        integerLogarithmicTerm t (N + 1 : ℕ) n := by
      symm
      simpa only [Nat.cast_add, Nat.cast_one, add_zero] using
        ford_integerLogarithmicPrefix_eq_source N (R - N) 0 t

theorem norm_pintz2023ExponentialBlock_le_length
    {N R : ℕ} (hNR : N ≤ R) (t : ℝ) :
    ‖pintz2023ExponentialBlock N R t‖ ≤ (R - N : ℕ) := by
  unfold pintz2023ExponentialBlock
  calc
    ‖∑ n ∈ Finset.Ioc N R, (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤
        ∑ n ∈ Finset.Ioc N R, ‖(n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ = ∑ _n ∈ Finset.Ioc N R, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnPos : 0 < n := by
        have := (Finset.mem_Ioc.mp hn).1
        omega
      change ‖(((n : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ = 1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hnPos)]
      simp
    _ = (R - N : ℕ) := by simp [Nat.card_Ioc, hNR]

/-- Exact selected A²B estimate in the nontrivial long-block branch. -/
theorem norm_pintz2023ExponentialBlock_sq_le_A2B_selected
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauHigh : tau ≤ 4)
    (hlong : classicalA2BFirstShift N tau +
        classicalA2BSecondShift N tau ≤ R - N) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ^ 2 ≤
      (2 * ((R - N : ℕ) : ℝ) / classicalA2BFirstShift N tau) *
        (((R - N : ℕ) : ℝ) +
          2 * logarithmicA2BInnerSumBound
            ((N : ℝ) ^ tau) (N + 1 : ℕ) (R - N)
              (classicalA2BFirstShift N tau)
              (classicalA2BSecondShift N tau)) := by
  let L := R - N
  let H₁ := classicalA2BFirstShift N tau
  let H₂ := classicalA2BSecondShift N tau
  have hNPos : 0 < N := by omega
  have hNOne : 1 ≤ N := by omega
  have hL : L ≤ N := by
    dsimp only [L]
    omega
  have hH₁pos : 0 < H₁ := classicalA2BFirstShift_pos hNOne htauHigh
  have hH₂pos : 0 < H₂ := classicalA2BSecondShift_pos hNOne htauHigh
  have hH₁ : H₁ ≤ L := by
    dsimp only [H₁, H₂, L] at hlong ⊢
    omega
  have hH₂ : H₂ ≤ L - (H₁ - 1) := by
    dsimp only [H₁, H₂, L] at hlong ⊢
    omega
  have hA : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hLA : (L : ℝ) ≤ (N + 1 : ℕ) := by
    exact_mod_cast hL.trans (Nat.le_add_right N 1)
  have ht : 0 < (N : ℝ) ^ tau := by positivity
  have hsmall :
      (N : ℝ) ^ tau * (H₁ : ℝ) * (H₂ : ℝ) /
          ((N + 1 : ℕ) : ℝ) ^ 4 ≤ 1 := by
    simpa only [H₁, H₂, Nat.cast_add, Nat.cast_one] using
      classicalA2B_curvature_small hNOne htauHigh
  have hraw := norm_logarithmic_sum_sq_le_A2B_compact
    ((N : ℝ) ^ tau) ((N + 1 : ℕ) : ℝ) L H₁ H₂
      ht hA hLA hH₁pos hH₁ hH₂pos hH₂ hsmall
  rw [pintz2023ExponentialBlock_eq_integerLogarithmicPrefix
    hNPos hNR.le ((N : ℝ) ^ tau)]
  simpa only [L, H₁, H₂, Nat.cast_add, Nat.cast_one] using hraw

#print axioms pintz2023ExponentialBlock_eq_integerLogarithmicPrefix
#print axioms norm_pintz2023ExponentialBlock_le_length
#print axioms norm_pintz2023ExponentialBlock_sq_le_A2B_selected

end

end GafniTao

import GafniTao.ClassicalA3BScale
import GafniTao.ClassicalA2BChosen

/-!
# Selected finite `A³B` estimate

The three rounded shifts are inserted into the exact outer theorem.  The
complementary short-block branch is intentionally deferred to optimization.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard
open scoped BigOperators

noncomputable section

theorem norm_pintz2023ExponentialBlock_sq_le_A3B_selected
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauHigh : tau ≤ 5)
    (hlong : classicalA3BFirstShift N tau +
        classicalA3BSecondShift N tau + classicalA3BThirdShift N tau ≤ R - N) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ^ 2 ≤
      (2 * ((R - N : ℕ) : ℝ) / classicalA3BFirstShift N tau) *
        (((R - N : ℕ) : ℝ) +
          2 * logarithmicA3BOuterSumBound
            ((N : ℝ) ^ tau) ((N : ℝ) + 1) (R - N)
              (classicalA3BFirstShift N tau)
              (classicalA3BSecondShift N tau)
              (classicalA3BThirdShift N tau)) := by
  let L := R - N
  let H₁ := classicalA3BFirstShift N tau
  let H₂ := classicalA3BSecondShift N tau
  let H₃ := classicalA3BThirdShift N tau
  have hNPos : 0 < N := by omega
  have hNOne : 1 ≤ N := by omega
  have hL : L ≤ N := by dsimp only [L]; omega
  have hH₁pos : 0 < H₁ := classicalA3BFirstShift_pos hNOne htauHigh
  have hH₂pos : 0 < H₂ := classicalA3BSecondShift_pos hNOne htauHigh
  have hH₃pos : 0 < H₃ := classicalA3BThirdShift_pos hNOne htauHigh
  have hH₁ : H₁ ≤ L := by dsimp only [H₁, H₂, H₃, L] at hlong ⊢; omega
  have hH₃ : H₃ ≤ L - (H₁ - 1) - (H₂ - 1) := by
    dsimp only [H₁, H₂, H₃, L] at hlong ⊢
    omega
  have hA : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hLA : (L : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hL.trans (Nat.le_add_right N 1)
  have ht : 0 < (N : ℝ) ^ tau := by positivity
  have hsmall :
      (N : ℝ) ^ tau * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) /
          ((N : ℝ) + 1) ^ 5 ≤ 1 := by
    simpa only [H₁, H₂, H₃] using classicalA3B_curvature_small hNOne htauHigh
  have hraw := logarithmic_weyl_A3B_process_summed
    ((N : ℝ) ^ tau) ((N : ℝ) + 1) L H₁ H₂ H₃
      ht hA hLA hH₁ hH₂pos hH₃pos hH₃ hsmall
  rw [pintz2023ExponentialBlock_eq_integerLogarithmicPrefix
    hNPos hNR.le ((N : ℝ) ^ tau)]
  have hH₁R : (0 : ℝ) < H₁ := by exact_mod_cast hH₁pos
  have hNH : (((L + H₁ : ℕ) : ℝ)) ≤ 2 * L := by
    norm_num
    exact_mod_cast (by omega : L + H₁ ≤ 2 * L)
  let S := logarithmicA3BOuterSumBound
    ((N : ℝ) ^ tau) ((N : ℝ) + 1) L H₁ H₂ H₃
  have hS : 0 ≤ S := by dsimp only [S, logarithmicA3BOuterSumBound]; positivity
  have hupper :
      (((L + H₁ : ℕ) : ℝ)) *
          ((H₁ : ℝ) * L + (H₁ : ℝ) * (2 * S)) ≤
        (H₁ : ℝ) ^ 2 *
          ((2 * (L : ℝ) / H₁) * ((L : ℝ) + 2 * S)) := by
    calc
      _ ≤ (2 * (L : ℝ)) *
          ((H₁ : ℝ) * L + (H₁ : ℝ) * (2 * S)) := by gcongr
      _ = (H₁ : ℝ) ^ 2 *
          ((2 * (L : ℝ) / H₁) * ((L : ℝ) + 2 * S)) := by
        field_simp [hH₁R.ne']
  have hsq := hraw.trans (by simpa only [S] using hupper)
  apply le_of_mul_le_mul_left (by
    simpa only [L, H₁, H₂, H₃, S, Nat.cast_add, Nat.cast_one, mul_assoc]
      using hsq)
  exact sq_pos_of_pos hH₁R

#print axioms norm_pintz2023ExponentialBlock_sq_le_A3B_selected

end

end GafniTao

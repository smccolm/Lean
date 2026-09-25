import TaoTrudgianYang2025.AtkinsonMainPartialSummation

/-! Removing the actual descending linear weight by exact finite Abel summation. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem norm_linear_weighted_range_le (a : ℕ → ℂ) (H : ℕ) (hH : 0 < H)
    (B : ℝ) (hp : ∀ L ≤ H, ‖∑ n ∈ Finset.range L, a n‖ ≤ B) :
    ‖∑ n ∈ Finset.range H, ((1-(n:ℝ)/H : ℝ):ℂ)*a n‖ ≤ B := by
  let w : ℕ → ℂ := fun n => ((1-(n:ℝ)/H : ℝ):ℂ)
  have hpos : (0:ℝ) < H := by exact_mod_cast hH
  have hlast : ‖w (H-1)‖ = 1/(H:ℝ) := by
    have he : 1-((H-1:ℕ):ℝ)/H = 1/(H:ℝ) := by
      rw [Nat.cast_sub (by omega),Nat.cast_one]
      field_simp
      ring
    dsimp only [w]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hdiff (n : ℕ) : ‖w (n+1)-w n‖ = 1/(H:ℝ) := by
    have he : w (n+1)-w n = ((-(1/(H:ℝ)):ℝ):ℂ) := by
      dsimp only [w]
      push_cast
      ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_neg,
      abs_of_nonneg (by positivity)]
  have hs := norm_sum_mul_le_discrete_parts w a H
  rw [hlast] at hs
  simp only [hdiff] at hs
  calc
    _ ≤ (1/(H:ℝ))*‖∑ n ∈ Finset.range H, a n‖+
        ∑ n ∈ Finset.range (H-1),
          (1/(H:ℝ))*‖∑ k ∈ Finset.range (n+1), a k‖ := hs
    _ ≤ (1/(H:ℝ))*B+∑ _n ∈ Finset.range (H-1), (1/(H:ℝ))*B := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hp H le_rfl) (by positivity)
      · apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hp (n+1) (by
          have ht := Finset.mem_range.mp hn
          omega)) (by positivity)
    _ = B := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [Nat.cast_sub (by omega),Nat.cast_one]
      field_simp
      ring

end TaoTrudgianYang2025

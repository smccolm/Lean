import TaoTrudgianYang2025.SargosSlowCharacter
import TaoTrudgianYang2025.AtkinsonMainPartialSummation

/-! Exact source-interval reindexing and Abel control by actual prefix sums. -/

noncomputable section

open GafniTao Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_sum_Ioc_eq_range {A : Type*} [AddCommMonoid A]
    (N H : ℕ) (f : ℤ → A) :
    (∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H), f n) =
      ∑ j ∈ Finset.range H, f ((N : ℤ)+j+1) := by
  symm
  refine Finset.sum_bij (fun j _ => (N : ℤ)+j+1) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    dsimp only
    rw [Finset.mem_Ioc]
    constructor <;> omega
  · intro j hj k hk he
    dsimp only at he
    omega
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : 0 ≤ n-(N : ℤ)-1 := by omega
    have hc := Int.toNat_of_nonneg hn0
    refine ⟨(n-(N : ℤ)-1).toNat,Finset.mem_range.mpr (by omega),?_⟩
    dsimp only
    omega
  · intro j hj
    rfl

theorem sargos_norm_weighted_prefix_le {N H : ℕ} (hH : H ≤ N)
    (a : ℤ → ℂ) (w : ℕ → ℂ) {B V : ℝ} (hB : 0 ≤ B)
    (hp : ∀ L ≤ N, ‖∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+L), a n‖ ≤ B)
    (hw : ‖w (H-1)‖ ≤ 1)
    (hv : ∑ j ∈ Finset.range (H-1), ‖w (j+1)-w j‖ ≤ V) :
    ‖∑ j ∈ Finset.range H, w j*a ((N : ℤ)+j+1)‖ ≤ (1+V)*B := by
  have hp' : ∀ L ≤ N, ‖∑ j ∈ Finset.range L, a ((N : ℤ)+j+1)‖ ≤ B := by
    intro L hL
    rw [← sargos_sum_Ioc_eq_range]
    exact hp L hL
  calc
    _ ≤ ‖w (H-1)‖*‖∑ j ∈ Finset.range H, a ((N : ℤ)+j+1)‖+
        ∑ j ∈ Finset.range (H-1),
          ‖w (j+1)-w j‖*‖∑ k ∈ Finset.range (j+1), a ((N : ℤ)+k+1)‖ :=
      norm_sum_mul_le_discrete_parts w (fun j => a ((N : ℤ)+j+1)) H
    _ ≤ B+∑ j ∈ Finset.range (H-1), ‖w (j+1)-w j‖*B := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left (hp' H hH) (norm_nonneg _)).trans
          (by simpa using mul_le_mul_of_nonneg_right hw hB)
      · apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        exact mul_le_mul_of_nonneg_left (hp' (j+1) (by omega)) (norm_nonneg _)
    _ = (1+(∑ j ∈ Finset.range (H-1), ‖w (j+1)-w j‖))*B := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add le_rfl hv) hB

theorem sargos_slow_character_variation {N H : ℕ} (hN : 1 ≤ N) (hH : H ≤ N)
    {K : ℝ} (hK : 0 ≤ K) {φ φ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc (N : ℝ) (2*N), HasDerivWithinAt φ (φ' x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' x‖ ≤ K/N) :
    (∑ j ∈ Finset.range (H-1),
      ‖fordAdditiveCharacter (φ ((N : ℝ)+(j+1)+1))-
        fordAdditiveCharacter (φ ((N : ℝ)+j+1))‖) ≤ 2*Real.pi*K := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  calc
    _ ≤ ∑ j ∈ Finset.range (H-1), 2*Real.pi*K/N := by
      apply Finset.sum_le_sum
      intro j hj
      exact sargos_slow_character_adjacent hφ hφ' (by
        have hj' := Finset.mem_range.mp hj
        omega)
    _ = ((H-1 : ℕ) : ℝ)*(2*Real.pi*K/N) := by simp
    _ ≤ (N : ℝ)*(2*Real.pi*K/N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (by omega : H-1 ≤ N)
    _ = _ := by field_simp

end TaoTrudgianYang2025

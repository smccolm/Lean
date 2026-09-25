import TaoTrudgianYang2025.DoubledBlockPrefixes
import TaoTrudgianYang2025.LinearWeightAbel

/-! An attained full doubled block controlling the actual linearly weighted sum. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem exists_doubled_block_weighted (a : ℕ → ℂ) (H : ℕ) (hH : 2 ≤ H)
    (ha0 : a 0 = 0) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ n < H, ‖a n‖ ≤ A) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖∑ n ∈ Finset.range H, ((1-(n:ℝ)/H : ℝ):ℂ)*a n‖ ≤
        (Nat.clog 2 H:ℝ)*(A+‖∑ j ∈ Finset.range k, a (k+j)‖) := by
  classical
  obtain ⟨k,hk,hmax⟩ := (Finset.Icc 1 (H/2)).exists_max_image
    (fun k => ‖∑ j ∈ Finset.range k, a (k+j)‖)
    (by exact ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩)
  have hk' := Finset.mem_Icc.mp hk
  refine ⟨k,by omega,by omega,?_⟩
  apply norm_linear_weighted_range_le a H (by omega)
  intro L hL
  apply norm_prefix_le_doubled_blocks a H (Nat.clog 2 H) L ha0 hL
    (hL.trans (Nat.le_pow_clog (by norm_num) H)) A
    ‖∑ j ∈ Finset.range k, a (k+j)‖ hA (norm_nonneg _) ha
  intro l hl hlH
  exact hmax l (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)

end TaoTrudgianYang2025

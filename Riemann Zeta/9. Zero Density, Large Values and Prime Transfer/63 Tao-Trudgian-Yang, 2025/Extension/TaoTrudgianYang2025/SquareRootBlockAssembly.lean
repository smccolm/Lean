import TaoTrudgianYang2025.IntegerBlockPartition
import TaoTrudgianYang2025.SquareRootBlockBudget

/-! Full interval cost of actual square-root blocks and the final partial block. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem euclidean_block_count_of_half_scale {N L : ℕ} {M R : ℝ}
    (hR : 0 < R) (hL : R/2 ≤ L) (hN : (N:ℝ) ≤ M) (hM : R ≤ M) :
    ((N/L:ℕ)+1:ℝ) ≤ 3*M/R := by
  have hd : ((N/L:ℕ):ℝ)*L ≤ N := by exact_mod_cast Nat.div_mul_le_self N L
  have hprod := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg (N/L))
  apply (le_div_iff₀ hR).mpr
  nlinarith

theorem norm_range_from_square_root_blocks
    (f : ℕ → ℂ) (N : ℕ) {M C D μ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hN : (N:ℝ) ≤ M) (hM : μ^(-(1:ℝ)/2) ≤ M)
    (hb : ∀ a n : ℕ, a+n ≤ N → n ≤ ⌊μ^(-(1:ℝ)/2)⌋₊ →
      ‖∑ j ∈ Finset.range n, f (a+j)‖ ≤
        40*C*(1+2*Real.pi*D)*μ^(-(5:ℝ)/12)) :
    ‖∑ j ∈ Finset.range N, f j‖ ≤ 120*C*(1+2*Real.pi*D)*M*μ^((1:ℝ)/12) := by
  let L := ⌊μ^(-(1:ℝ)/2)⌋₊
  obtain ⟨hLp,hLlo,_⟩ := square_root_block_floor hμ hμ1
  have hsplit := norm_sum_range_of_block_bounds f N L
    (fun k hk => hb (k*L) L (by
      have hk1 : k+1 ≤ N/L := by omega
      have hm := Nat.mul_le_mul_right L hk1
      have hd := Nat.div_mul_le_self N L
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega) le_rfl)
    (hb ((N/L)*L) (N%L) (by rw [Nat.div_add_mod'])
      (Nat.le_of_lt (Nat.mod_lt N hLp)))
  have hc := euclidean_block_count_of_half_scale
    (N := N) (L := L) (Real.rpow_pos_of_pos hμ _) hLlo hN hM
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 40*C*(1+2*Real.pi*D)*μ^(-(5:ℝ)/12) by positivity)
  apply hsplit.trans (hm.trans_eq ?_)
  have hp : μ^(-(5:ℝ)/12)/μ^(-(1:ℝ)/2) = μ^((1:ℝ)/12) := by
    rw [← Real.rpow_sub hμ]
    congr 1
    ring
  calc
    _ = 120*C*(1+2*Real.pi*D)*M*(μ^(-(5:ℝ)/12)/μ^(-(1:ℝ)/2)) := by ring
    _ = _ := by rw [hp]

end TaoTrudgianYang2025

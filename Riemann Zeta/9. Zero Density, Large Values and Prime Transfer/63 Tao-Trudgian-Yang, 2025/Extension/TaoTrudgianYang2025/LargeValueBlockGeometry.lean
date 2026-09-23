import TaoTrudgianYang2025.FiniteBlockCoefficients

/-! Actual disjoint natural blocks inside the closed source dyadic interval. -/

open Finset

noncomputable section

namespace TaoTrudgianYang2025

def largeValueBlock (N L j : ℕ) : Finset ℕ :=
  Ico (N+j*L) (N+(j+1)*L)

def largeValueBlockBasis (N L : ℕ) : List (ℕ → ℂ) :=
  (range (N/L)).toList.map
    (fun j n => if n ∈ largeValueBlock N L j then (1:ℂ) else 0)

theorem largeValueBlock_card (N L j : ℕ) :
    (largeValueBlock N L j).card = L := by
  simp only [largeValueBlock,Nat.card_Ico,Nat.add_mul,Nat.one_mul]
  omega

theorem largeValueBlock_subset (N L j : ℕ) (hj : j < N/L) :
    largeValueBlock N L j ⊆ Icc N (2*N) := by
  intro n hn
  have hp := mem_Ico.mp hn
  have hm : (j+1)*L ≤ N := (Nat.mul_le_mul_right L (Nat.succ_le_of_lt hj)).trans
    (Nat.div_mul_le_self N L)
  exact mem_Icc.mpr ⟨by omega,by omega⟩

theorem largeValueBlock_unique {N L j k n : ℕ}
    (hj : n ∈ largeValueBlock N L j) (hk : n ∈ largeValueBlock N L k) :
    j = k := by
  have hp := mem_Ico.mp hj
  have hq := mem_Ico.mp hk
  rcases lt_trichotomy j k with h | h | h
  · have hm := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
    change (j+1)*L ≤ k*L at hm
    omega
  · exact h
  · have hm := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
    change (k+1)*L ≤ j*L at hm
    omega

theorem largeValueBlockBasis_norm_sum (N L n : ℕ) :
    ((largeValueBlockBasis N L).map (fun b => ‖b n‖)).sum ≤ 1 := by
  classical
  simp only [largeValueBlockBasis,List.map_map,Function.comp_def,apply_ite,norm_one,norm_zero]
  rw [sum_map_toList,sum_boole]
  have hc : ({j ∈ range (N/L) | n ∈ largeValueBlock N L j}).card ≤ 1 := by
    apply card_le_one.mpr
    intro j hj k hk
    exact largeValueBlock_unique (mem_filter.mp hj).2 (mem_filter.mp hk).2
  exact_mod_cast hc

theorem largeValueBlock_evaluation (N L j : ℕ) (hj : j < N/L) (w : ℕ → ℂ) :
    finiteCoefficientEvaluation (Icc N (2*N)) w
      (fun n => if n ∈ largeValueBlock N L j then 1 else 0) =
      ∑ n ∈ largeValueBlock N L j, w n := by
  simp only [finiteCoefficientEvaluation,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
    ite_mul,one_mul,zero_mul,← sum_filter]
  rw [filter_mem_eq_inter,inter_eq_right.mpr (largeValueBlock_subset N L j hj)]

end TaoTrudgianYang2025

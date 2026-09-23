import TaoTrudgianYang2025.LargeValueBlockCoherence

/-! Exact block coverage and the variance of the actual block indicators. -/

open Finset

namespace TaoTrudgianYang2025

theorem largeValueBlocks_cover_half {N L : ℕ} (hL : 0 < L) (hLN : L ≤ N) :
    N ≤ 2*((N/L)*L) := by
  have hq : 0 < N/L := Nat.div_pos hLN hL
  have hm := Nat.mod_lt N hL
  have he := Nat.mod_add_div N L
  have hp := Nat.mul_le_mul_right L (show 1 ≤ N/L by omega)
  nlinarith

theorem largeValueBlockBasis_variance {N L : ℕ}
    (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    {t : ℝ} (ht : 0 ≤ t) (hheight : t ≤ (N:ℝ)/(2*(L:ℝ))) :
    (N:ℝ)*(L:ℝ)/8 ≤
      ((largeValueBlockBasis N L).map (fun b => Complex.normSq
        (∑ n ∈ Icc N (2*N), b n*dirichletPhase n t))).sum := by
  classical
  have hblock (j : ℕ) :
      (L:ℝ)^2/4 ≤ Complex.normSq (∑ n ∈ largeValueBlock N L j, dirichletPhase n t) := by
    have h := largeValueBlock_sum_lower (j:=j) hN hL ht hheight
    rw [Complex.normSq_eq_norm_sq]
    have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (L:ℝ)/2) h 2
    nlinarith
  have hcoverage : (N:ℝ) ≤ 2*((N/L:ℕ):ℝ)*(L:ℝ) := by
    have hc : N ≤ 2*(N/L)*L := by
      simpa only [mul_assoc] using largeValueBlocks_cover_half hL hLN
    exact_mod_cast hc
  have hbase : (N:ℝ)*(L:ℝ)/8 ≤ ((N/L:ℕ):ℝ)*((L:ℝ)^2/4) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoverage (Nat.cast_nonneg L : (0:ℝ) ≤ L)]
  apply hbase.trans
  simp only [largeValueBlockBasis,List.map_map,Function.comp_def]
  rw [sum_map_toList]
  calc
    ((N/L:ℕ):ℝ)*((L:ℝ)^2/4) = ∑ _j ∈ range (N/L), (L:ℝ)^2/4 := by simp
    _ ≤ _ := sum_le_sum (fun j hj => by
      change (L:ℝ)^2/4 ≤ Complex.normSq
        (finiteCoefficientEvaluation (Icc N (2*N)) (fun n => dirichletPhase n t)
          (fun n => if n ∈ largeValueBlock N L j then 1 else 0))
      rw [largeValueBlock_evaluation N L j (mem_range.mp hj)]
      exact hblock j)

end TaoTrudgianYang2025

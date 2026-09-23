import TaoTrudgianYang2025.SargosCProcessHighScale

/-! Actual short-support and bounded-optimum branches of the C-process. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem sargos_closed_source_norm_le_length (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ) :
    ‖exponentialSumAt F T N a (a+M)‖ ≤ (M:ℝ)+1 := by
  have h := norm_exponentialSumAt_le_card F T N a (a+M)
  have hc : (Finset.Icc a (a+M)).card = M+1 := by rw [Nat.card_Icc]; omega
  simpa only [hc,Nat.cast_add,Nat.cast_one] using h

theorem sargos_short_source_twelfth_bound (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ) {R : ℝ}
    (hR : 1 ≤ R) (hMR : (M:ℝ) ≤ R) (hpower : R^13 ≤ N^12) :
    ‖exponentialSumAt F T N a (a+M)‖^12 ≤ 4096*(N^12/R) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hn : ‖exponentialSumAt F T N a (a+M)‖ ≤ 2*R :=
    (sargos_closed_source_norm_le_length F T N a M).trans (by linarith)
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 12
  have hr : R^12 ≤ N^12/R := by
    apply (le_div_iff₀ hRp).mpr
    simpa only [← pow_succ] using hpower
  have hh := mul_le_mul_of_nonneg_left hr (show (0:ℝ) ≤ 4096 by norm_num)
  norm_num only [mul_pow,show (2:ℝ)^12 = 4096 by norm_num] at hp
  exact hp.trans hh

theorem sargos_bounded_optimum_twelfth_bound (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ) {R : ℝ}
    (hN : 1 ≤ N) (hb : (a:ℝ)+M ≤ 2*N) (hR : 0 < R) (hR2 : R ≤ 2) :
    ‖exponentialSumAt F T N a (a+M)‖^12 ≤ (2*(3:ℝ)^12)*(N^12/R) := by
  have hn : ‖exponentialSumAt F T N a (a+M)‖ ≤ 3*N := by
    have h := norm_exponentialSumAt_le_add_one F T N a (a+M)
    push_cast at h
    linarith
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 12
  have hr : N^12 ≤ 2*(N^12/R) := by
    rw [show 2*(N^12/R) = (2*N^12)/R by ring]
    apply (le_div_iff₀ hR).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hR2 (show 0 ≤ N^12 by positivity)]
  have hh := mul_le_mul_of_nonneg_left hr (show (0:ℝ) ≤ 3^12 by positivity)
  calc
    _ ≤ 3^12*N^12 := by simpa only [mul_pow] using hp
    _ ≤ 3^12*(2*(N^12/R)) := hh
    _ = _ := by ring

theorem sargosCProcessScale_high_thirteenth {k l T N : ℝ}
    (hkl : InExponentPairTriangle k l) (hN : 1 ≤ N)
    (hhigh : N^(sargosCProcessThreshold k l) ≤ T) :
    (sargosCProcessScale k l T N)^13 ≤ N^12 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hhigh
  have hR := sargosCProcessScale_pos (k := k) (l := l) hTp hNp
  have hc := sargosCProcessScale_high_cap hkl hN hhigh
  calc
    _ ≤ (N^(2/3-1/100:ℝ))^13 := pow_le_pow_left₀ hR.le hc 13
    _ = N^((2/3-1/100:ℝ)*13) := (Real.rpow_mul_natCast hNp.le _ _).symm
    _ ≤ N^(12:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ = _ := Real.rpow_natCast _ _

end TaoTrudgianYang2025

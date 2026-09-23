import TaoTrudgianYang2025.SargosCProcessMainError

/-! The physical optimizing cost and all epsilon losses enter the exact C-process target. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosCProcess_target_factor {k l ε T N : ℝ} (hT : 0 < T) (hN : 0 < N) :
    (T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε) =
      ((T/N)^(sargosCProcessK k)*N^(sargosCProcessL k l))*((T/N)^ε*N^ε) := by
  rw [Real.rpow_add (div_pos hT hN),Real.rpow_add hN]
  ring

theorem sargosCProcess_cost_error_le_target {k l ε T N : ℝ}
    (hk : 0 ≤ k) (hε : 0 ≤ ε) (hN : 1 ≤ N) (hNT : N ≤ T) :
    (N^12/sargosCProcessScale k l T N)*(T/N)^ε*N^(2*ε) ≤
      ((T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε))^12 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := hNp.trans_le hNT
  have hR := sargosCProcessScale_pos (k := k) (l := l) hTp hNp
  have hU : 1 ≤ T/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNT)
  have he := sargosCProcess_epsilon_budget hU hN hε
  calc
    _ = (N^12/sargosCProcessScale k l T N)*((T/N)^ε*N^(2*ε)) := by ring
    _ ≤ (N^12/sargosCProcessScale k l T N)*((T/N)^ε*N^ε)^12 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by
      rw [sargosCProcessScale_cost hk hTp hNp,sargosCProcess_target_factor hTp hNp]
      simp only [mul_pow]

theorem sargosCProcess_cost_le_target {k l ε T N : ℝ}
    (hk : 0 ≤ k) (hε : 0 ≤ ε) (hN : 1 ≤ N) (hNT : N ≤ T) :
    N^12/sargosCProcessScale k l T N ≤
      ((T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε))^12 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := hNp.trans_le hNT
  have hR := sargosCProcessScale_pos (k := k) (l := l) hTp hNp
  have hU : 1 ≤ T/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNT)
  have h1 := Real.one_le_rpow hU hε
  have h2 := Real.one_le_rpow hN (show 0 ≤ 2*ε by linarith)
  have hmul := one_le_mul_of_one_le_of_one_le h1 h2
  calc
    _ ≤ (N^12/sargosCProcessScale k l T N)*((T/N)^ε*N^(2*ε)) :=
      le_mul_of_one_le_right (by positivity) hmul
    _ = (N^12/sargosCProcessScale k l T N)*(T/N)^ε*N^(2*ε) := by ring
    _ ≤ _ := sargosCProcess_cost_error_le_target hk hε hN hNT

end TaoTrudgianYang2025

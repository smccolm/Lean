import TaoTrudgianYang2025.SargosCProcessMainError
import TaoTrudgianYang2025.SargosCProcessIntegerChoice

/-! Every term of the genuine finite estimate fits the optimizing cost and epsilon budget. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosCProcess_finite_budget {k l ε D T N H : ℝ}
    (hk : 0 ≤ k) (hε : 0 ≤ ε) (hD : 0 < D) (hN : 1 ≤ N) (hNT : N ≤ T)
    (hH : 0 < H) (hHR : H ≤ sargosCProcessScale k l T N) (hHN : H ≤ N)
    (hHL : sargosCProcessScale k l T N/2 ≤ H) (hsecondary : N^4 ≤ T*H^3) :
    (N^12/H+N^11*(D*T*H^4/N^5)^(k+ε)*N^(l+ε)+N^16/(D*T*H^4))*H^ε ≤
      (2+D^(k+ε)+2/D)*(N^12/sargosCProcessScale k l T N)*(T/N)^ε*N^(2*ε) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := hNp.trans_le hNT
  have hR := sargosCProcessScale_pos (k := k) (l := l) hTp hNp
  have hU : 1 ≤ T/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNT)
  let A := N^12/sargosCProcessScale k l T N
  let Q := (T/N)^ε*N^ε
  have hA : 0 < A := by dsimp [A]; positivity
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hU hε) (Real.one_le_rpow hN hε)
  have hfirst := sargosCProcess_first_term_le hNp hR hHL
  have hsecond := sargosCProcess_secondary_term_le hD hTp hNp hH hsecondary
  have hmain := sargosCProcess_main_error_bound hk hε hD hTp hNp hH hHR hHN
  have hf : N^12/H ≤ 2*A*Q := by
    calc
      _ ≤ 2*A := hfirst
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hQ
  have hs : N^16/(D*T*H^4) ≤ (2/D)*A*Q := by
    calc
      _ ≤ (1/D)*(N^12/H) := hsecond
      _ ≤ (1/D)*(2*A) := mul_le_mul_of_nonneg_left hfirst (by positivity)
      _ = (2/D)*A := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hQ
  have hm : N^11*(D*T*H^4/N^5)^(k+ε)*N^(l+ε) ≤ D^(k+ε)*A*Q := by
    simpa only [Q,mul_assoc] using hmain
  have hb :
      N^12/H+N^11*(D*T*H^4/N^5)^(k+ε)*N^(l+ε)+N^16/(D*T*H^4) ≤
        (2+D^(k+ε)+2/D)*A*Q := by nlinarith only [hf,hs,hm]
  have hp := Real.rpow_le_rpow hH.le hHN hε
  calc
    _ ≤ ((2+D^(k+ε)+2/D)*A*Q)*N^ε :=
      mul_le_mul hb hp (by positivity) (by positivity)
    _ = (2+D^(k+ε)+2/D)*A*(T/N)^ε*(N^ε*N^ε) := by dsimp [Q]; ring
    _ = _ := by rw [← Real.rpow_add hNp,show ε+ε = 2*ε by ring]

end TaoTrudgianYang2025

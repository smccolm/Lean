import TaoTrudgianYang2025.SargosModelCorrelationBound
import TaoTrudgianYang2025.SargosInteriorDifferencing

/-! Exact finite-scale bookkeeping for the genuine correlation estimate. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargos_finite_process_algebra {N H E A B C D : ℝ}
    (hH : 1 ≤ H) (hHN : H ≤ N) (hE : 1 ≤ E)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 1 ≤ D) :
    1492992*(N/H)^6*N^6+
      (382205952*N^11/H^4)*(C*(N*H^3*E+H^4*E*A+B*E))+D*N^11*E ≤
      (1492992+382205952*C+D)*(N^12/H+N^11*A+N^11*B/H^4)*E := by
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hNp : 0 < N := hHp.trans_le hHN
  have hEp : 0 ≤ E := zero_le_one.trans hE
  let K := N^12/H+N^11*A+N^11*B/H^4
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbase : N^12/H ≤ K := by
    have ha : 0 ≤ N^11*A := by positivity
    have hb : 0 ≤ N^11*B/H^4 := by positivity
    dsimp [K]
    linarith only [ha,hb]
  have hpow : H ≤ H^6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hH (show 1 ≤ 6 by norm_num)
  have hdiag : (N/H)^6*N^6 ≤ K*E := by
    calc
      _ = N^12/H^6 := by field_simp
      _ ≤ N^12/H := div_le_div_of_nonneg_left (by positivity) hHp hpow
      _ ≤ K := hbase
      _ ≤ K*E := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hE hK
  have hlinear : N^11 ≤ N^12/H := by
    apply (le_div_iff₀ hHp).mpr
    calc
      _ ≤ N^11*N := mul_le_mul_of_nonneg_left hHN (by positivity)
      _ = _ := by ring
  have herr : N^11*E ≤ K*E := mul_le_mul_of_nonneg_right (hlinear.trans hbase) hEp
  have hmain :
      (382205952*N^11/H^4)*(C*(N*H^3*E+H^4*E*A+B*E)) =
        (382205952*C)*K*E := by
    dsimp [K]
    field_simp
  rw [hmain]
  have hd := mul_le_mul_of_nonneg_left hdiag (show (0:ℝ) ≤ 1492992 by norm_num)
  have he := mul_le_mul_of_nonneg_left herr (show 0 ≤ D by linarith)
  nlinarith only [hd,he]

end TaoTrudgianYang2025

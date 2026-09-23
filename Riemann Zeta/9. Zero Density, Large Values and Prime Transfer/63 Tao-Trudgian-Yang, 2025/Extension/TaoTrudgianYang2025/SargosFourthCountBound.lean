import TaoTrudgianYang2025.SargosHyperbolaCount

/-!
# The Robert--Sargos fourth-power near-count bound

An explicit O(N squared log N) bound for the actual source solution set.
No moment inequality or C-process estimate is assumed.
-/

namespace TaoTrudgianYang2025

theorem sargos_hyperbola_scale_bound {N : ℝ} (hN : 1 ≤ N) :
    4*(4*N+1+11*N*(1+Real.log (2*N))) ≤
      108*N*(1+Real.log N) := by
  have hNpos : 0 < N := by linarith
  have hlog := Real.log_nonneg hN
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hloss : 1+Real.log (2*N) ≤ 2*(1+Real.log N) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hNpos)]
    linarith
  have hm := mul_le_mul_of_nonneg_left hloss (by positivity : 0 ≤ 11*N)
  nlinarith [mul_nonneg (le_of_lt hNpos) hlog]

theorem card_sargosFourthNearSolutions_le_log {N : ℕ} (hN : 1 ≤ N) :
    ((sargosFourthNearSolutions N).card : ℝ) ≤
      4096*(N : ℝ)^2*(1+Real.log N) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hsig : ((sargosSignedHyperbola (2*N) (11*N)).card : ℝ) ≤
      108*(N : ℝ)*(1+Real.log N) := by
    have h := card_sargosSignedHyperbola_le (2*N) (11*N)
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at h
    rw [show (2 : ℝ)*(2*(N : ℝ)) = 4*N by ring] at h
    exact h.trans (sargos_hyperbola_scale_bound hNreal)
  calc
    _ ≤ (2*(N : ℝ)+1)*7*((sargosSignedHyperbola (2*N) (11*N)).card : ℝ) := by
      exact_mod_cast card_sargosFourthNearSolutions_le_hyperbola hN
    _ ≤ (21*(N : ℝ))*(108*(N : ℝ)*(1+Real.log N)) := by
      apply mul_le_mul (by linarith : (2*(N : ℝ)+1)*7 ≤ 21*N) hsig
        (Nat.cast_nonneg _) (by positivity)
    _ ≤ _ := by
      nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) hlog]

end TaoTrudgianYang2025

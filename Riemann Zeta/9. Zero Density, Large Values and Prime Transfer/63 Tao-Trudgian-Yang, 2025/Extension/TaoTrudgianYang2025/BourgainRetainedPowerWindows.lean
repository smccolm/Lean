import TaoTrudgianYang2025.BourgainRetainedUniform

/-!
# Physical power algebra for the retained-zeta source estimate

All three terms use the same physical N,T,V and the same retained moment.
The zeta term is never replaced by a freely chosen cardinality estimate.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_retained_power_identity {N : ℝ} (hN : 0 < N) (s τ M : ℝ) :
    N^2/(N^s)^2+(N^τ)^2*N^4/(N^s)^8+
      N^3*Real.sqrt M/(N^s)^4 =
        N^(2-2*s)+N^(2*τ+4-8*s)+N^(3-4*s)*Real.sqrt M := by
  have hpow (a : ℝ) (m : ℕ) : (N^a)^m = N^(a*(m : ℝ)) :=
    (Real.rpow_mul_natCast hN.le a m).symm
  rw [hpow,hpow,hpow,hpow]
  have h3 : N^3*Real.sqrt M/N^(s*(4 : ℕ)) =
      (N^3/N^(s*(4 : ℕ)))*Real.sqrt M := by ring
  rw [h3, ← Real.rpow_two, ← Real.rpow_natCast N 4, ← Real.rpow_natCast N 3,
    ← Real.rpow_sub hN, ← Real.rpow_add hN,
    ← Real.rpow_sub hN, ← Real.rpow_sub hN]
  norm_num only [Nat.cast_ofNat]
  ring_nf

/-- Actual power windows bound the diagonal, pole and retained-zeta terms. -/
theorem bourgain_retained_power_terms_le {N T V σ τ δ M : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T)
    (hTu : T ≤ N^(τ+δ)) (hVl : N^(σ-2*δ) ≤ V-1) :
    N^2/(V-1)^2 + T^2*N^4/(V-1)^8 + N^3*Real.sqrt M/(V-1)^4 ≤
      N^(2-2*σ+4*δ) + N^(2*τ+4-8*σ+18*δ) +
        N^(3-4*σ+8*δ)*Real.sqrt M := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ N^2/(N^(σ-2*δ))^2 +
        (N^(τ+δ))^2*N^4/(N^(σ-2*δ))^8 +
        N^3*Real.sqrt M/(N^(σ-2*δ))^4 := by gcongr
    _ = _ := by
      rw [bourgain_retained_power_identity hNp]
      ring_nf

end TaoTrudgianYang2025

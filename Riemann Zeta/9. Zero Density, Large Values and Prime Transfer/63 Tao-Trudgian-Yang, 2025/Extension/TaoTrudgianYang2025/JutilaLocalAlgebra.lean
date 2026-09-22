import TaoTrudgianYang2025.JutilaLocalCardinality

/-!
# Exact source-scale algebra for the local Jutila estimate

The factors two, three and four are retained in explicit constants.
No source endpoint loss or physical power is dropped.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- Exact expansion of the solved local cardinality expression. -/
theorem jutila_local_cardinality_expand (k : ℕ) (N T V Z : ℝ) (hV : 1 < V) :
    jutilaLocalCardinalityBound k N T V Z =
      (72*Z)*N^2/(V-1)^2 +
      (4*Z^2*(4 : ℝ)^(2*k)*(3 : ℝ)^(4*k))*T^k*N^(2*k)/(V-1)^(4*k) +
      (4*Z^3*(4 : ℝ)^(4*k)*(2 : ℝ)^(2*k)*(3 : ℝ)^(8*k))*
        T*N^(6*k)/(V-1)^(8*k) := by
  have hv : V-1 ≠ 0 := by linarith
  unfold jutilaLocalCardinalityBound
  simp only [div_pow, mul_pow, ← pow_mul]
  field_simp
  ring

/-- Exact normalization of the physical absorption condition. -/
theorem jutila_local_absorption_identity (k : ℕ) (N T B ν : ℝ) :
    (2*(B*T^ν*(4*N)^(2*k))*(2*N)^k)*(3 : ℝ)^(4*k) =
      (2*B*(4 : ℝ)^(2*k)*(2 : ℝ)^k*(3 : ℝ)^(4*k))*T^ν*N^(3*k) := by
  simp only [mul_pow, pow_mul]
  ring

/-- The three successive smoothing factors have their actual height
powers, rather than three unrelated losses. -/
theorem jutila_local_smoothing_powers {T B ν : ℝ} (hT : 0 < T) :
    (B*T^ν)^2 = B^2*T^(2*ν) ∧ (B*T^ν)^3 = B^3*T^(3*ν) := by
  constructor
  · rw [mul_pow, ← Real.rpow_mul_natCast hT.le]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm ν (2 : ℝ)]
  · rw [mul_pow, ← Real.rpow_mul_natCast hT.le]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm ν (3 : ℝ)]

end TaoTrudgianYang2025

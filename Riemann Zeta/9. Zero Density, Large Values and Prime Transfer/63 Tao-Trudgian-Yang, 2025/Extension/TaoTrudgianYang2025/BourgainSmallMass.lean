import TaoTrudgianYang2025.BourgainRetainedSource

/-!
# The elementary recurrence in Bourgain's small-mass branch

The quarter-power identities include zero cardinality. The moment bound
below is a genuine scalar deduction; the actual source-pattern consumer
is supplied separately.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- Solving the three-quarter-power recurrence keeps the actual fourth cost. -/
theorem bourgain_three_quarter_recurrence {R A B : ℝ}
    (hR : 0 ≤ R) (hA : 0 ≤ A) (h : R ≤ A+B*R^(3/4 : ℝ)) :
    R ≤ 2*A+16*B^4 := by
  by_cases hsmall : R ≤ 2*A
  · exact hsmall.trans (by nlinarith [pow_nonneg (sq_nonneg B) 2])
  have hRp : 0 < R := by linarith
  let x := R^(1/4 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hRp _
  have hx4 : x^4 = R := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hR]
    norm_num
  have hx3 : x^3 = R^(3/4 : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hR]
    norm_num
  have hp : x^3*x ≤ x^3*(2*B) := by
    rw [← hx3, ← hx4] at h
    rw [← hx4] at hsmall
    nlinarith
  have hxb : x ≤ 2*B := le_of_mul_le_mul_left hp (pow_pos hx 3)
  have hb := pow_le_pow_left₀ hx.le hxb 4
  rw [hx4] at hb
  nlinarith

/-- Square-root normalization of the actual small zeta-mass threshold. -/
theorem bourgain_small_mass_sqrt_le {N R M α τ : ℝ}
    (hN : 0 < N) (hR : 0 ≤ R)
    (hm : M ≤ N^(-α)*R^(3/2 : ℝ)*N^(τ/2)) :
    Real.sqrt M ≤ N^(-α/2+τ/4)*R^(3/4 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, hm.trans_eq ?_⟩
  rw [mul_pow, ← Real.rpow_mul_natCast hN.le, ← Real.rpow_mul_natCast hR]
  norm_num only [Nat.cast_ofNat]
  rw [show (-α/2+τ/4)*2 = -α+τ/2 by ring, Real.rpow_add hN]
  ring

/-- Eliminating the retained small-mass term gives the exact three powers
that precede Bourgain's subdivision and parameter optimization. -/
theorem bourgain_small_mass_power_bound {N R C σ τ α ν M : ℝ}
    (hN : 0 < N) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hm : M ≤ N^(-α)*R^(3/2 : ℝ)*N^(τ/2))
    (hr : R ≤ C*(N^(2-2*σ+ν)+N^(2*τ+4-8*σ+ν)+N^(3-4*σ+ν)*Real.sqrt M)) :
    R ≤ (2*C)*N^(2-2*σ+ν)+(2*C)*N^(2*τ+4-8*σ+ν)+
      (16*C^4)*N^(-2*α+τ+12-16*σ+4*ν) := by
  have hs := bourgain_small_mass_sqrt_le hN hR hm
  let A := C*(N^(2-2*σ+ν)+N^(2*τ+4-8*σ+ν))
  let B := C*N^(3-4*σ+ν)*N^(-α/2+τ/4)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrec : R ≤ A+B*R^(3/4 : ℝ) := by
    calc
      _ ≤ C*(N^(2-2*σ+ν)+N^(2*τ+4-8*σ+ν)+
          N^(3-4*σ+ν)*(N^(-α/2+τ/4)*R^(3/4 : ℝ))) := hr.trans (by gcongr)
      _ = _ := by dsimp [A,B]; ring
  have hpow : B^4 = C^4*N^(-2*α+τ+12-16*σ+4*ν) := by
    dsimp [B]
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hN.le,
      ← Real.rpow_mul_natCast hN.le, mul_assoc, ← Real.rpow_add hN]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  have hb := bourgain_three_quarter_recurrence hR hA hrec
  rw [hpow] at hb
  convert hb using 1; dsimp [A]; ring

end TaoTrudgianYang2025

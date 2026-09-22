import TaoTrudgianYang2025.BourgainCommonLevels

/-!
# Shared polynomial scales for the correlation grid

A coarse polynomial bound is used only to construct a common positive
correlation floor. The selection loss will still be bounded logarithmically.
-/

open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- A coarse bound for the actual ceiling-log amplitude count. -/
theorem bourgainZetaBandCount_crude_power_bound {B N U A u : ℝ}
    (hB : 0 < B) (hN : 1 ≤ N) (hU : 0 ≤ U) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (hcap : U ≤ 3*N^u) :
    (bourgainZetaBandCount B U (N^(-A)) : ℝ) ≤ (4*B+2)*N^(u+A) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let M := Nat.ceil (B*(1+U)/(N^(-A)))
  have hX : 0 < B*(1+U)/(N^(-A)) := by positivity
  have hp : 1 ≤ N^(u+A) := Real.one_le_rpow hN (by positivity)
  have hpu : 1 ≤ N^u := Real.one_le_rpow hN hu
  have hinput : B*(1+U)/(N^(-A)) ≤ 4*B*N^(u+A) := by
    calc
      _ = B*(1+U)*N^A := by rw [Real.rpow_neg hNp.le, div_inv_eq_mul]
      _ ≤ B*(4*N^u)*N^A := by gcongr; linarith
      _ = _ := by rw [Real.rpow_add hNp]; ring
  have hceil := Nat.ceil_lt_add_one hX.le
  have hclog : Nat.clog 2 M ≤ M := Nat.clog_le_of_le_pow M.lt_two_pow_self.le
  have hc : (Nat.clog 2 M : ℝ) ≤ (M : ℝ) := by exact_mod_cast hclog
  rw [bourgainZetaBandCount, Nat.cast_add, Nat.cast_one]
  change (Nat.clog 2 M : ℝ)+1 ≤ _
  dsimp only [M] at hc
  nlinarith

def bourgainCorrelationGrowthExponent (α τ ε : ℝ) : ℝ :=
  2*(|τ|+1)+2*(|τ|+ε+1+bourgainSharedFloorExponent α τ ε)+
    (|τ|+ε+1)*(1+ε)

def bourgainCorrelationExponent (α τ ε : ℝ) : ℝ :=
  |α|+|τ|+bourgainCorrelationGrowthExponent α τ ε+1

def bourgainCorrelationConstant (B C ε : ℝ) : ℝ :=
  4096*C*(4*B+2)^2*(3 : ℝ)^(1+ε)+1

def bourgainCorrelationFloor (N B C α τ ε : ℝ) : ℝ :=
  N^(-bourgainCorrelationExponent α τ ε)/bourgainCorrelationConstant B C ε

theorem bourgainCorrelationGrowthExponent_nonneg (α τ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ bourgainCorrelationGrowthExponent α τ ε := by
  have ha := (bourgainSharedFloorExponent_pos α τ hε).le
  dsimp only [bourgainCorrelationGrowthExponent]
  positivity

theorem bourgainCorrelationExponent_pos (α τ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 < bourgainCorrelationExponent α τ ε := by
  have he := bourgainCorrelationGrowthExponent_nonneg α τ hε
  dsimp only [bourgainCorrelationExponent]
  positivity

theorem bourgainCorrelationConstant_one_le (B : ℝ) {C : ℝ} (hC : 0 ≤ C) (ε : ℝ) :
    1 ≤ bourgainCorrelationConstant B C ε := by
  dsimp only [bourgainCorrelationConstant]
  have hh : 0 ≤ 4096*C*(4*B+2)^2*(3 : ℝ)^(1+ε) := by positivity
  linarith

theorem bourgainCorrelationFloor_pos {N B C α τ ε : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) :
    0 < bourgainCorrelationFloor N B C α τ ε := by
  have hK : 0 < bourgainCorrelationConstant B C ε :=
    zero_lt_one.trans_le (bourgainCorrelationConstant_one_le B hC ε)
  exact div_pos (Real.rpow_pos_of_pos hN _) hK

/-- The exponent margin works for all real alpha and tau. -/
theorem bourgain_correlation_floor_exponent {α τ ε : ℝ} (hε : 0 ≤ ε) :
    bourgainCorrelationGrowthExponent α τ ε-2*bourgainCorrelationExponent α τ ε ≤
      -2*α+τ := by
  have he := bourgainCorrelationGrowthExponent_nonneg α τ hε
  dsimp only [bourgainCorrelationExponent]
  nlinarith [le_abs_self α, neg_le_abs τ, abs_nonneg τ]

/-- The common inverse-power floor is small enough for the coarse
physical product coefficient. This is algebra, not an analytic premise. -/
theorem bourgain_correlation_floor_balance {N B C α τ ε : ℝ}
    (hN : 1 ≤ N) (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    (bourgainCorrelationConstant B C ε-1)*N^(bourgainCorrelationGrowthExponent α τ ε)*
      (bourgainCorrelationFloor N B C α τ ε)^2 ≤ N^(-2*α)*N^τ := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let K := bourgainCorrelationConstant B C ε
  let A := bourgainCorrelationExponent α τ ε
  let E := bourgainCorrelationGrowthExponent α τ ε
  have hK : 0 < K := zero_lt_one.trans_le (bourgainCorrelationConstant_one_le B hC ε)
  have hratio : (K-1)/K^2 ≤ 1 := by
    apply (div_le_one (pow_pos hK 2)).mpr
    nlinarith [sq_nonneg (K-1)]
  have hsq : (bourgainCorrelationFloor N B C α τ ε)^2 = N^(-2*A)/K^2 := by
    dsimp only [bourgainCorrelationFloor]
    rw [div_pow, ← Real.rpow_mul_natCast hNp.le]
    congr 2
    norm_num
    ring
  calc
    _ = ((K-1)/K^2)*N^(E-2*A) := by
      rw [hsq, Real.rpow_sub hNp]
      rw [show -2*A = -(2*A) by ring, Real.rpow_neg hNp.le]
      dsimp only [K, A, E]
      ring
    _ ≤ N^(E-2*A) := mul_le_of_le_one_left (Real.rpow_nonneg hNp.le _) hratio
    _ ≤ N^(-2*α+τ) := Real.rpow_le_rpow_of_exponent_le hN (bourgain_correlation_floor_exponent hε)
    _ = _ := Real.rpow_add hNp _ _

end TaoTrudgianYang2025

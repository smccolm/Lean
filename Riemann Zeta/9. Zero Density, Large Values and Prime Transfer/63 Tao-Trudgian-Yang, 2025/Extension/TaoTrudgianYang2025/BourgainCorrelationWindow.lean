import TaoTrudgianYang2025.BourgainCorrelationScales

/-!
# The actual component correlation lies in a common physical window

The lower endpoint is derived from the actual mass/fourth-moment product;
the upper endpoint follows from occupancy and integer-window overlap.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Actual retained cardinality, amplitude count and spatial enlargement
bound the full correlation-product coefficient by one shared power. -/
theorem bourgain_correlation_coefficient_bound (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) (hW : 0 < W.card)
    {B C α τ ε δ : ℝ} (hB : 0 < B) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    let U := P.T+P.N^(ε/8)+1
    let J := bourgainZetaBandCount B U (P.N^(-bourgainSharedFloorExponent α τ ε))
    1024*(Nat.log 2 W.card+1 : ℕ)^2*(J : ℝ)^2*C*U^(1+ε) ≤
      (bourgainCorrelationConstant B C ε-1)*P.N^(bourgainCorrelationGrowthExponent α τ ε) := by
  let u := |τ|+ε+1
  let A := bourgainSharedFloorExponent α τ ε
  let U := P.T+P.N^(ε/8)+1
  let J := bourgainZetaBandCount B U (P.N^(-A))
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hUp : 0 < U := by
    dsimp only [U]
    have ht := P.T_pos
    positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hA : 0 ≤ A := (bourgainSharedFloorExponent_pos α τ hε).le
  have hU := bourgain_shared_band_radius_le P hε hδ hT
  have hJ : (J : ℝ) ≤ (4*B+2)*P.N^(u+A) :=
    bourgainZetaBandCount_crude_power_bound hB P.one_lt_N.le hUp.le hA hu hU
  have hlog : Nat.log 2 W.card+1 ≤ W.card :=
    Nat.succ_le_iff.mpr (Nat.log_lt_self 2 hW.ne')
  have hlogR : ((Nat.log 2 W.card+1 : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hlog
  have hZ := hlogR.trans (bourgain_retained_card_le_shared_power P hsub hδ hT)
  have hproduct : (P.N^(|τ|+1))^2*(P.N^(u+A))^2*(P.N^u)^(1+ε) =
      P.N^(bourgainCorrelationGrowthExponent α τ ε) := by
    rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_mul_natCast hNp.le,
      ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
    congr 1
    dsimp only [bourgainCorrelationGrowthExponent, u, A]
    norm_num
    ring
  change 1024*(Nat.log 2 W.card+1 : ℕ)^2*(J : ℝ)^2*C*U^(1+ε) ≤ _
  calc
    _ ≤ 1024*(2*P.N^(|τ|+1))^2*((4*B+2)*P.N^(u+A))^2*C*(3*P.N^u)^(1+ε) := by
      gcongr
    _ = 4096*C*(4*B+2)^2*(3 : ℝ)^(1+ε)*
        ((P.N^(|τ|+1))^2*(P.N^(u+A))^2*(P.N^u)^(1+ε)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Real.rpow_nonneg hNp.le u)]
      ring
    _ = _ := by
      rw [hproduct]
      dsimp only [bourgainCorrelationConstant]
      ring

/-- Every actual selected component has correlation above the common
inverse-power floor and below four times the physical window radius. -/
theorem bourgain_component_correlation_window (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates)
    {B C α τ ε δ : ℝ} {j q : ℕ}
    (hband : BourgainComponentBand P.N P.T B C τ α ε W j q)
    (hB : 0 < B) (hC : 0 < C) (hε : 0 ≤ ε)
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    let H := P.N^(ε/8)
    let U := P.T+H+1
    let a := P.N^(-bourgainSharedFloorExponent α τ ε)
    let r := bourgainZetaBandCorrelation (bourgainDifferenceLevel W j) H U (a*(2 : ℝ)^q)
    0 < bourgainCorrelationFloor P.N B C α τ ε ∧
      bourgainCorrelationFloor P.N B C α τ ε < r ∧ r ≤ 4*H := by
  let H := P.N^(ε/8)
  let U := P.T+H+1
  let a := P.N^(-bourgainSharedFloorExponent α τ ε)
  let J := bourgainZetaBandCount B U a
  let r := bourgainZetaBandCorrelation (bourgainDifferenceLevel W j) H U (a*(2 : ℝ)^q)
  let G := (bourgainCorrelationConstant B C ε-1)*
    P.N^(bourgainCorrelationGrowthExponent α τ ε)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hpow := hband.2.2.1
  have hW : 0 < W.card := (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le hpow
  have hdata := hband.2.2.2.2.2
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, hr, _, hupper, _⟩
  have hrel : (2 : ℝ)^j ≤ 2*(1 : ℝ)*(W.card : ℝ) := by
    have hh : (2 : ℝ)^j ≤ (W.card : ℝ) := by exact_mod_cast hpow
    nlinarith [Nat.cast_nonneg (α := ℝ) W.card]
  have hprod := hband.relative_correlation_lower hNp hrel
  change P.N^(-2*α)*P.N^τ <
    1024*(Nat.log 2 W.card+1 : ℕ)^2*(J : ℝ)^2*C*U^(1+ε)*1*r^2 at hprod
  rw [mul_one] at hprod
  have hcoef := bourgain_correlation_coefficient_bound P hsub hW (α := α) hB hC.le hε hδ hT
  have hcoarse : P.N^(-2*α)*P.N^τ < G*r^2 :=
    hprod.trans_le (mul_le_mul_of_nonneg_right hcoef (sq_nonneg r))
  have hbalance := bourgain_correlation_floor_balance (B := B) (C := C)
    (α := α) (τ := τ) P.one_lt_N.le hC.le hε
  have hG : 0 < G := by
    dsimp only [G, bourgainCorrelationConstant]
    rw [add_sub_cancel_right]
    positivity
  have hf := bourgainCorrelationFloor_pos (B := B) (α := α) (τ := τ) (ε := ε) hNp hC.le
  have hsq : (bourgainCorrelationFloor P.N B C α τ ε)^2 < r^2 :=
    (mul_lt_mul_iff_of_pos_left hG).mp (hbalance.trans_lt hcoarse)
  refine ⟨hf, (sq_lt_sq₀ hf.le (le_of_lt hr)).mp hsq, ?_⟩
  have hH : 1 ≤ H := Real.one_le_rpow P.one_lt_N.le (by positivity)
  have hceil : (Nat.ceil H : ℝ) ≤ H+1 := (Nat.ceil_lt_add_one (by linarith)).le
  change r^2 ≤ 2*H*(2*Nat.ceil H+1 : ℕ) at hupper
  push_cast at hupper
  apply (sq_le_sq₀ (le_of_lt hr) (by positivity : 0 ≤ 4*H)).mp
  nlinarith

end TaoTrudgianYang2025

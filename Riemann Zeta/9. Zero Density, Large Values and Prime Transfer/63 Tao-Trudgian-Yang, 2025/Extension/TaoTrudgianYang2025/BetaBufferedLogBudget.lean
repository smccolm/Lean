import TaoTrudgianYang2025.BetaBufferedSharpSource

/-!
# Uniform polynomial budgets for the actual sharp-source logarithms

The integer core endpoints and the prescribed far-tail radius are bounded
from the original model envelope. These estimates keep their physical
N,T dependence and include floor/ceiling and empty-log conventions.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem modelPhaseCore_natAbs_bounds
    {σ δ T N : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hT : 0 ≤ T) (hN : 1 ≤ N) :
    ((modelPhaseCoreLower σ δ T N).natAbs : ℝ) ≤ T+1 ∧
      ((modelPhaseCoreUpper δ T N).natAbs : ℝ) ≤ 2*T+1 := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hK : 0 ≤ T/N := div_nonneg hT hNpos.le
  have hK₁ : T/N ≤ T := div_le_self hT hN
  have hp : 0 ≤ (2 : ℝ)^(-σ) := Real.rpow_nonneg (by norm_num) _
  have hp₁ : (2 : ℝ)^(-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have ha₀ : -(T/N) ≤ (T/N)*((2 : ℝ)^(-σ)-δ) := by
    have h := mul_le_mul_of_nonneg_left (show (-1 : ℝ) ≤ (2 : ℝ)^(-σ)-δ by linarith) hK
    nlinarith
  have ha₁ : (T/N)*((2 : ℝ)^(-σ)-δ) ≤ T/N := by
    have h := mul_le_mul_of_nonneg_left (show (2 : ℝ)^(-σ)-δ ≤ 1 by linarith) hK
    simpa only [mul_one] using h
  have hb₀ : 0 ≤ (T/N)*(1+δ) := by positivity
  have hb₁ : (T/N)*(1+δ) ≤ 2*T := by nlinarith
  have hfa := Int.floor_le ((T/N)*((2 : ℝ)^(-σ)-δ))
  have hfa' := Int.lt_floor_add_one ((T/N)*((2 : ℝ)^(-σ)-δ))
  have hcb := Int.le_ceil ((T/N)*(1+δ))
  have hcb' := Int.ceil_lt_add_one ((T/N)*(1+δ))
  simp only [Nat.cast_natAbs,Int.cast_abs]
  unfold modelPhaseCoreLower modelPhaseCoreUpper
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem modelPhaseSharpRadius_le_polynomial
    {σ δ T N C : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hT : 0 ≤ T) (hN : 1 ≤ N) (hC : 0 ≤ C) :
    ((⌈C*T*(1+T)^2/N⌉₊+(modelPhaseCoreLower σ δ T N).natAbs+
      (modelPhaseCoreUpper δ T N).natAbs+1 : ℕ) : ℝ) ≤
      (C+4)*(T+1)^3 := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hX : 0 ≤ C*T*(1+T)^2/N := by positivity
  have hceil := Nat.ceil_lt_add_one hX
  have hc := modelPhaseCore_natAbs_bounds hσ hδ hδ₁ hT hN
  have hdiv := div_le_self (show 0 ≤ C*T*(1+T)^2 by positivity) hN
  have hm := mul_le_mul_of_nonneg_left (show T ≤ T+1 by linarith)
    (show 0 ≤ C*(T+1)^2 by positivity)
  have hXupper : C*T*(1+T)^2/N ≤ C*(T+1)^3 := by nlinarith
  have hp : T+1 ≤ (T+1)^3 := by
    nlinarith [sq_nonneg T,mul_nonneg hT (sq_nonneg T)]
  push_cast
  nlinarith [hc.1,hc.2]

theorem log_nat_le_polynomial_budget
    {n : ℕ} {K T : ℝ} (hK : 1 ≤ K) (hT : 0 ≤ T)
    (hn : (n : ℝ) ≤ K*(T+1)^3) :
    Real.log (n : ℝ) ≤ Real.log K+3*Real.log (T+1) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hTpos : 0 < T+1 := by linarith
  by_cases hz : n = 0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    have hlK := Real.log_nonneg hK
    have hlT := Real.log_nonneg (show 1 ≤ T+1 by linarith)
    linarith
  · have h := Real.log_le_log (show 0 < (n : ℝ) by exact_mod_cast Nat.pos_of_ne_zero hz) hn
    rw [Real.log_mul hKpos.ne' (pow_ne_zero _ hTpos.ne'),Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h

theorem modelPhaseSharpFarLengths_le_polynomial
    {σ δ T N C : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hT : 0 ≤ T) (hN : 1 ≤ N) (hC : 0 ≤ C) :
    let A := modelPhaseCoreLower σ δ T N
    let B := modelPhaseCoreUpper δ T N
    let R : ℕ := ⌈C*T*(1+T)^2/N⌉₊+A.natAbs+B.natAbs+1
    (((A+(R : ℤ)).toNat : ℕ) : ℝ) ≤ (C+6)*(T+1)^3 ∧
      ((((R : ℤ)-B).toNat : ℕ) : ℝ) ≤ (C+6)*(T+1)^3 := by
  intro A B R
  have hc := modelPhaseCore_natAbs_bounds hσ hδ hδ₁ hT hN
  have hr : (R : ℝ) ≤ (C+4)*(T+1)^3 :=
    modelPhaseSharpRadius_le_polynomial hσ hδ hδ₁ hT hN hC
  have ha : (A : ℝ) ≤ (A.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using le_abs_self (A : ℝ)
  have hb : -(B : ℝ) ≤ (B.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using neg_le_abs (B : ℝ)
  have hzA : 0 ≤ A+(R : ℤ) := by dsimp [R]; omega
  have hzB : 0 ≤ (R : ℤ)-B := by dsimp [R]; omega
  have heA : ((A+(R : ℤ)).toNat : ℝ) = (A : ℝ)+(R : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hzA
  have heB : (((R : ℤ)-B).toNat : ℝ) = (R : ℝ)-(B : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hzB
  rw [heA,heB]
  have hp : T+1 ≤ (T+1)^3 := by
    nlinarith [sq_nonneg T,mul_nonneg hT (sq_nonneg T)]
  have hcA : (A.natAbs : ℝ) ≤ T+1 := hc.1
  have hcB : (B.natAbs : ℝ) ≤ 2*T+1 := hc.2
  constructor <;> nlinarith

theorem modelPhaseBufferedInnerLengths_le
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hflat : l+4*η < r) :
    let A := modelPhaseCoreLower σ δ T N
    let B := modelPhaseCoreUpper δ T N
    let L := modelPhaseBufferedSupportLower F r η T N
    let U := modelPhaseBufferedSupportUpper F l η T N
    let P := modelPhaseBufferedPlateauLower F r η T N
    let Q := modelPhaseBufferedPlateauUpper F l η T N
    ((L-A).toNat : ℝ) ≤ 3*(T/N)+3 ∧
      ((B-U).toNat : ℝ) ≤ 3*(T/N)+3 ∧
      ((Q-P-1).toNat : ℝ) ≤ 3*(T/N)+3 := by
  intro A B L U P Q
  have hi := modelPhaseBufferedSupport_inside_core hσ hδ hF hT hN hη hl hr hflat
  have he := modelPhaseBufferedBand_endpoints hσ hδ hF hT hN hη hl hr hflat
  have hAL : A ≤ L := hi.1
  have hUB : U ≤ B := hi.2
  have hLP : L ≤ P := he.1
  have hPU : P ≤ U := he.2.1
  have hLQ : L ≤ Q := he.2.2.1
  have hQU : Q ≤ U := he.2.2.2
  have hc := modelPhaseCore_card_le hσ.le (approximateModelPhase_tolerance_nonneg hF)
    (hδ.trans (min_le_right _ _)) hT.le hN
  have hleft : (Finset.Ico A L).card ≤ (Finset.Icc A B).card := by
    apply Finset.card_le_card
    intro q hq
    simp only [Finset.mem_Ico,Finset.mem_Icc] at hq ⊢
    omega
  have hright : (Finset.Ioc U B).card ≤ (Finset.Icc A B).card := by
    apply Finset.card_le_card
    intro q hq
    simp only [Finset.mem_Ioc,Finset.mem_Icc] at hq ⊢
    omega
  have hmid : (Finset.Ioo P Q).card ≤ (Finset.Icc A B).card := by
    apply Finset.card_le_card
    intro q hq
    simp only [Finset.mem_Ioo,Finset.mem_Icc] at hq ⊢
    omega
  rw [Int.card_Ico] at hleft
  rw [Int.card_Ioc] at hright
  rw [Int.card_Ioo] at hmid
  exact ⟨(Nat.cast_le.mpr hleft).trans hc,(Nat.cast_le.mpr hright).trans hc,
    (Nat.cast_le.mpr hmid).trans hc⟩

theorem three_scale_le_polynomial_budget {C T N : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hN : 1 ≤ N) :
    3*(T/N)+3 ≤ (C+6)*(T+1)^3 := by
  have hd := div_le_self hT hN
  have hp : T+1 ≤ (T+1)^3 := by
    nlinarith [sq_nonneg T,mul_nonneg hT (sq_nonneg T)]
  have hc := mul_nonneg hC (pow_nonneg (show 0 ≤ T+1 by linarith) 3)
  nlinarith

end TaoTrudgianYang2025

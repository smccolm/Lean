import TaoTrudgianYang2025.BourgainFamilySlice
import Mathlib.Analysis.MeanInequalities

/-!
# Elimination of the common multiplicity and correlation levels

The actual component product lower bound supplies a level-free cardinality
coefficient. The second coefficient cancels multiplicity exactly. The finite
bin count controls the sum of three-halves powers, including an empty family.
-/

open Finset RiemannZeta.GuthMaynard
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

def bourgainEliminatedCardCoefficient (N L B C τ α ε : ℝ) : ℝ :=
  N^(-2*α)*N^τ /
    (32768*N^(ε/8)*(2*Nat.ceil (N^(ε/8))+1 : ℕ)*
      (bourgainDifferenceLogLoss N τ)^2*
      (bourgainZetaBandCount B (L+N^(ε/8)+1)
        (N^(-bourgainSharedFloorExponent α τ ε)) : ℝ)^2*
      C*(L+N^(ε/8)+1)^(1+ε))

/-- The common product bound on a genuine retained component removes its
unknown correlation and multiplicity from the first mixed coefficient. -/
theorem bourgain_component_card_coefficient
    (P : LargeValuePattern) {L : ℝ} (hL : 0 < L) (i : ℕ) (W : Finset ℝ)
    (hsub : W ⊆ (P.localized L hL i).reflectedOrdinates)
    {B C τ α ε δ s d : ℝ} {j q : ℕ}
    (hC : 0 < C) (hδ : δ ≤ 1) (hT : L ≤ P.N^(τ+δ))
    (hband : BourgainComponentBand P.N L B C τ α ε W j q)
    (hd : 0 < d)
    (hproduct : P.N^(-2*α)*P.N^τ <
      4096*(Nat.log 2 W.card+1 : ℕ)^2*
        (bourgainZetaBandCount B (L+P.N^(ε/8)+1)
          (P.N^(-bourgainSharedFloorExponent α τ ε)) : ℝ)^2*
        C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) :
    bourgainEliminatedCardCoefficient P.N L B C τ α ε <
      d*bourgainSliceCardCoefficient P.N ε s := by
  let H := P.N^(ε/8)
  let U := L+H+1
  let K := (2*Nat.ceil H+1 : ℕ)
  let Z := bourgainDifferenceLogLoss P.N τ
  let J := (bourgainZetaBandCount B U
    (P.N^(-bourgainSharedFloorExponent α τ ε)) : ℝ)
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hH : 0 < H := Real.rpow_pos_of_pos hN _
  have hU : 0 < U := by dsimp only [U]; linarith
  have hK : (0 : ℝ) < K := by dsimp only [K]; positivity
  have hZ : 0 < Z := bourgainDifferenceLogLoss_pos P.one_lt_N.le τ
  have hJ : 0 < J := by
    dsimp only [J]
    exact_mod_cast bourgainZetaBandCount_pos B U (P.N^(-bourgainSharedFloorExponent α τ ε))
  have hR : 0 < W.card :=
    (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le hband.2.2.1
  have hlog : (Nat.log 2 W.card+1 : ℕ) ≤ Z :=
    bourgain_retained_difference_level_count (P.localized L hL i) hsub hR hδ hT
  have hlog2 : ((Nat.log 2 W.card+1 : ℕ) : ℝ)^2 ≤ Z^2 :=
    pow_le_pow_left₀ (by positivity) hlog 2
  have hp : P.N^(-2*α)*P.N^τ < 4096*Z^2*J^2*C*U^(1+ε)*d*s^2 := by
    calc
      _ < 4096*(Nat.log 2 W.card+1 : ℕ)^2*J^2*C*U^(1+ε)*d*s^2 := hproduct
      _ = ((Nat.log 2 W.card+1 : ℕ) : ℝ)^2*
          (4096*J^2*C*U^(1+ε)*d*s^2) := by ring
      _ ≤ Z^2*(4096*J^2*C*U^(1+ε)*d*s^2) :=
        mul_le_mul_of_nonneg_right hlog2 (by positivity)
      _ = _ := by ring
  have hden : 0 < 32768*H*(K : ℝ)*Z^2*J^2*C*U^(1+ε) := by positivity
  change P.N^(-2*α)*P.N^τ/(32768*H*(K : ℝ)*Z^2*J^2*C*U^(1+ε)) <
    d*(s^2/(8*H*(K : ℝ)))
  apply (div_lt_iff₀ hden).mpr
  have heq : d*(s^2/(8*H*(K : ℝ)))*(32768*H*(K : ℝ)*Z^2*J^2*C*U^(1+ε)) =
      4096*Z^2*J^2*C*U^(1+ε)*d*s^2 := by
    field_simp [hH.ne', hK.ne']
    ring
  rw [heq]
  exact hp

/-- Multiplicity cancels exactly, without estimating it or assuming positivity
of the other denominators. -/
theorem bourgain_slice_sqrt_coefficient_cancel
    (N L B C τ α ε d : ℝ) (hd : d ≠ 0) :
    d*bourgainSliceSqrtCoefficient N L B C τ α ε d =
      bourgainSliceSqrtCoefficient N L B C τ α ε 1 := by
  unfold bourgainSliceSqrtCoefficient bourgainMassCoefficient
  simp only [mul_one]
  rw [show 32*bourgainDifferenceLogLoss N τ*
      (bourgainZetaBandCount B (L+N^(ε/8)+1)
        (N^(-bourgainSharedFloorExponent α τ ε)) : ℝ)*d*
      Real.sqrt (C*(L+N^(ε/8)+1)^(1+ε)) =
      (32*bourgainDifferenceLogLoss N τ*
        (bourgainZetaBandCount B (L+N^(ε/8)+1)
          (N^(-bourgainSharedFloorExponent α τ ε)) : ℝ)*
        Real.sqrt (C*(L+N^(ε/8)+1)^(1+ε)))*d by ring]
  have hcancel (x A B : ℝ) : d*(x/(A*d)/B) = x/A/B := by
    calc
      _ = (d*d⁻¹)*(x/A/B) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [mul_inv_cancel₀ hd, one_mul]
  exact hcancel _ _ _

/-- The source bin-count loss for the actual sum of component cardinalities. -/
theorem bourgain_sum_three_halves {ι : Type*} (A I : Finset ι) (hAI : A ⊆ I)
    (R : ι → ℝ) (hR : ∀ i ∈ A, 0 ≤ R i) :
    (∑ i ∈ A, R i)^(3/2 : ℝ) ≤
      Real.sqrt (I.card : ℝ)*(∑ i ∈ A, (R i)^(3/2 : ℝ)) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (f := R) A
    (by norm_num : (1 : ℝ) ≤ 3/2) hR
  norm_num only [show (3/2 : ℝ)-1 = 1/2 by norm_num] at h
  rw [← Real.sqrt_eq_rpow] at h
  have hcard : (A.card : ℝ) ≤ I.card := by exact_mod_cast Finset.card_le_card hAI
  exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcard)
    (Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hR i hi) _)))

theorem bourgainEliminatedCardCoefficient_pos {N L B C τ α ε : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 < C) :
    0 < bourgainEliminatedCardCoefficient N L B C τ α ε := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hH : 0 < N^(ε/8) := Real.rpow_pos_of_pos hNp _
  have hU : 0 < L+N^(ε/8)+1 := by linarith
  have hZ := bourgainDifferenceLogLoss_pos hN τ
  have hJ : (0 : ℝ) < bourgainZetaBandCount B (L+N^(ε/8)+1)
      (N^(-bourgainSharedFloorExponent α τ ε)) := by
    exact_mod_cast bourgainZetaBandCount_pos B (L+N^(ε/8)+1)
      (N^(-bourgainSharedFloorExponent α τ ε))
  unfold bourgainEliminatedCardCoefficient
  positivity

theorem bourgainSliceSqrtCoefficient_one_pos {N L B C τ α ε : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 < C) :
    0 < bourgainSliceSqrtCoefficient N L B C τ α ε 1 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hH : 0 < N^(ε/8) := Real.rpow_pos_of_pos hNp _
  have hU : 0 < L+N^(ε/8)+1 := by linarith
  have hZ := bourgainDifferenceLogLoss_pos hN τ
  have hJ : (0 : ℝ) < bourgainZetaBandCount B (L+N^(ε/8)+1)
      (N^(-bourgainSharedFloorExponent α τ ε)) := by
    exact_mod_cast bourgainZetaBandCount_pos B (L+N^(ε/8)+1)
      (N^(-bourgainSharedFloorExponent α τ ε))
  unfold bourgainSliceSqrtCoefficient bourgainMassCoefficient
  positivity

end TaoTrudgianYang2025

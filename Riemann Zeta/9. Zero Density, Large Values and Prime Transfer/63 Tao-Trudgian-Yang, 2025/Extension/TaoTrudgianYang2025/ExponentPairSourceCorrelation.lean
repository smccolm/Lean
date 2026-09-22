import TaoTrudgianYang2025.ExponentPairShiftUniformity
import TaoTrudgianYang2025.BetaStationaryMain

/-!
# Actual source correlations as compressed-model sums

The finite closed source block is reindexed by the literal integer shift.
Conjugation and the physical scales sigma*T*r/N and N-r are exact.
-/

noncomputable section

open Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem aProcessShiftPhase_character {F : ℝ → ℝ} {σ T N r m : ℝ}
    (hN : N ≠ 0) (hNr : N-r ≠ 0) (hσ : σ ≠ 0) (hr : r ≠ 0) :
    starRingEnd ℂ (oscillatory F T N m)*oscillatory F T N (m+r) =
      starRingEnd ℂ (oscillatory (aProcessShiftPhase F σ (r/N))
        (σ*T*r/N) (N-r) (m-r)) := by
  unfold oscillatory
  rw [aProcessShiftPhase_physical hN hNr hσ hr,mul_sub,sub_eq_add_neg,
    AddChar.map_add_eq_mul,AddChar.map_neg_eq_inv,Circle.coe_mul,Circle.coe_inv_eq_conj,
    map_mul (starRingEnd ℂ),Complex.conj_conj]

def sourceShiftCorrelation (F : ℝ → ℝ) (T N : ℝ) (a L r : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (L+1-r),
    starRingEnd ℂ (oscillatory F T N ((a : ℝ)+j))*
      oscillatory F T N ((a : ℝ)+j+r)

theorem sourceShiftCorrelation_empty (F : ℝ → ℝ) (T N : ℝ) (a L r : ℕ)
    (hr : L < r) : sourceShiftCorrelation F T N a L r = 0 := by
  simp [sourceShiftCorrelation,show L+1-r = 0 by omega]

theorem sourceShiftCorrelation_compressed_sum {F : ℝ → ℝ} {σ T N : ℝ}
    {a L r : ℕ} (hN : N ≠ 0) (hNr : N-(r : ℝ) ≠ 0)
    (hσ : σ ≠ 0) (hr : 0 < r) (hra : r ≤ a) (hrL : r ≤ L) :
    sourceShiftCorrelation F T N a L r =
      starRingEnd ℂ (exponentialSumAt (aProcessShiftPhase F σ ((r : ℝ)/N))
        (σ*T*r/N) (N-r) (a-r) ((a-r)+(L-r))) := by
  have hrR : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  rw [exponentialSumAt_eq_range,map_sum]
  unfold sourceShiftCorrelation
  rw [show L+1-r = (L-r)+1 by omega]
  apply Finset.sum_congr rfl
  intro j _
  have he := aProcessShiftPhase_character (F := F) (T := T)
    (r := (r : ℝ)) (m := (a : ℝ)+j) hN hNr hσ hrR
  rw [show (a : ℝ)+j-(r : ℝ) = ((a-r : ℕ) : ℝ)+j by
    rw [Nat.cast_sub hra]; ring] at he
  exact he

theorem norm_sourceShiftCorrelation_compressed_sum {F : ℝ → ℝ} {σ T N : ℝ}
    {a L r : ℕ} (hN : N ≠ 0) (hNr : N-(r : ℝ) ≠ 0)
    (hσ : σ ≠ 0) (hr : 0 < r) (hra : r ≤ a) (hrL : r ≤ L) :
    ‖sourceShiftCorrelation F T N a L r‖ =
      ‖exponentialSumAt (aProcessShiftPhase F σ ((r : ℝ)/N))
        (σ*T*r/N) (N-r) (a-r) ((a-r)+(L-r))‖ := by
  rw [sourceShiftCorrelation_compressed_sum hN hNr hσ hr hra hrL]
  exact norm_star _

theorem sourceShiftCorrelation_compressed_endpoints {N : ℝ} {a L r : ℕ}
    (ha : N ≤ (a : ℝ)) (hb : ((a+L : ℕ) : ℝ) ≤ 2*N)
    (hrN : (r : ℝ) < N) (hrL : r ≤ L) :
    N-(r : ℝ) ≤ ((a-r : ℕ) : ℝ) ∧
      (((a-r)+(L-r) : ℕ) : ℝ) ≤ 2*(N-r) := by
  have hra : r ≤ a := by exact_mod_cast (hrN.le.trans ha)
  rw [Nat.cast_add] at hb
  rw [Nat.cast_add,Nat.cast_sub hra,Nat.cast_sub hrL]
  constructor <;> linarith

end TaoTrudgianYang2025

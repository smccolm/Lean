import TaoTrudgianYang2025.ExponentPairLowFrequencyCore

/-! Closed-source first-derivative estimate, retaining all boundary terms. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

def modelPhaseFirstDerivativeConstant (σ : ℝ) : ℝ :=
  2/(2 : ℝ)^(-σ)+3

theorem modelPhaseFirstDerivativeConstant_pos (σ : ℝ) :
    0 < modelPhaseFirstDerivativeConstant σ := by
  unfold modelPhaseFirstDerivativeConstant
  positivity

theorem norm_exponentialSumAt_le_firstDerivative
    {σ δ T N : ℝ} {F : ℝ → ℝ} {a b : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hslope : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hcurv : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hscale : T ≤ N/4) :
    ‖exponentialSumAt F T N a b‖ ≤ modelPhaseFirstDerivativeConstant σ*(N/T) := by
  have hratio : 1 ≤ N/T := (le_div_iff₀ hT).mpr (by linarith)
  let K : ℝ := 2/(2 : ℝ)^(-σ)
  have hK : 0 < K := by dsimp [K]; positivity
  change ‖exponentialSumAt F T N a b‖ ≤ (K+3)*(N/T)
  by_cases hlong : a+3 ≤ b
  · obtain ⟨L,hL⟩ := Nat.exists_eq_add_of_le hlong
    have hbeq : b = a+L+3 := by omega
    have hbreal : (b : ℝ) = (a : ℝ)+(L : ℝ)+3 := by exact_mod_cast hbeq
    have hcore := norm_modelPhaseCore_le_firstDerivative (A := (a : ℝ)+1) (L := L)
      hσ hT hN hslope hcurv hF (by linarith) (by linarith) hscale
    have hboundary := norm_sum_Icc_le_interior_add_three
      (fun n => oscillatory F T N n) (fun n => (norm_oscillatory F T N n).le) a L
    rw [← hbeq] at hboundary
    have hboundary' : ‖exponentialSumAt F T N a b‖ ≤
        ‖∑ n ∈ Finset.range (L+1), oscillatory F T N ((a : ℝ)+1+n)‖+3 := by
      simpa only [exponentialSumAt,Nat.cast_add,Nat.cast_one] using hboundary
    calc
      _ ≤ K*(N/T)+3 := by linarith
      _ ≤ _ := by nlinarith
  · have hcard : (Finset.Icc a b).card ≤ 3 := by
      rw [Nat.card_Icc]
      omega
    have hsmall := (norm_exponentialSumAt_le_card F T N a b).trans
      (show ((Finset.Icc a b).card : ℝ) ≤ 3 by exact_mod_cast hcard)
    nlinarith

end TaoTrudgianYang2025

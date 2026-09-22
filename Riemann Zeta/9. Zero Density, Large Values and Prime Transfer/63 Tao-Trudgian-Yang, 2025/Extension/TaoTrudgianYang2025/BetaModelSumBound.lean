import TaoTrudgianYang2025.BetaFiniteSum

/-! Uniform second-derivative bound for the actual closed-interval
ANTEDB model-phase sum, including all endpoints. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

def modelPhaseSumConstant (σ : ℝ) : ℝ :=
  betaBProcessConstant (2*Real.pi*modelPhaseCurvatureLower σ)
    (2*Real.pi*(σ+1))+3

theorem modelPhaseSumConstant_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseSumConstant σ := by
  have hc : 0 < 2*Real.pi*modelPhaseCurvatureLower σ :=
    mul_pos (by positivity) (modelPhaseCurvatureLower_pos hσ)
  have hC : 0 ≤ 2*Real.pi*(σ+1) := by positivity
  have hk := betaBProcessConstant_pos hc hC
  unfold modelPhaseSumConstant
  linarith

theorem norm_exponentialSumAt_le_secondDerivative
    {σ δ T N : ℝ} {F : ℝ → ℝ} {a b : ℕ}
    (hσ : 0 < σ) (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hscale : T ≤ N^2) :
    ‖exponentialSumAt F T N a b‖ ≤
      modelPhaseSumConstant σ*(Real.sqrt T+N/Real.sqrt T) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hsqrt : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT
  have hsum : 1 ≤ Real.sqrt T+N/Real.sqrt T := by
    have : 0 ≤ N/Real.sqrt T := by positivity
    linarith
  let K := betaBProcessConstant (2*Real.pi*modelPhaseCurvatureLower σ)
    (2*Real.pi*(σ+1))
  have hK : 0 < K := betaBProcessConstant_pos
    (mul_pos (by positivity) (modelPhaseCurvatureLower_pos hσ)) (by positivity)
  change ‖exponentialSumAt F T N a b‖ ≤
    (K+3)*(Real.sqrt T+N/Real.sqrt T)
  by_cases hlong : a+3 ≤ b
  · obtain ⟨L,hL⟩ := Nat.exists_eq_add_of_le hlong
    have hbeq : b = a+L+3 := by omega
    have hbreal : (b : ℝ) = (a : ℝ)+(L : ℝ)+3 := by exact_mod_cast hbeq
    have hcore := norm_modelPhaseCore_le (A := (a : ℝ)+1) (L := L)
      hσ hTpos hNpos hδ hF (by linarith) (by linarith)
      (by linarith) hscale
    have hboundary := norm_sum_Icc_le_interior_add_three
      (fun n => oscillatory F T N n) (fun n => (norm_oscillatory F T N n).le) a L
    rw [← hbeq] at hboundary
    have hboundary' : ‖exponentialSumAt F T N a b‖ ≤
        ‖∑ n ∈ Finset.range (L+1), oscillatory F T N ((a : ℝ)+1+n)‖+3 := by
      simpa only [exponentialSumAt,Nat.cast_add,Nat.cast_one] using hboundary
    calc
      _ ≤ K*(Real.sqrt T+N/Real.sqrt T)+3 := by linarith
      _ ≤ _ := by nlinarith
  · have hcard : (Finset.Icc a b).card ≤ 3 := by
      rw [Nat.card_Icc]
      omega
    have hsmall := (norm_exponentialSumAt_le_card F T N a b).trans
      (show ((Finset.Icc a b).card : ℝ) ≤ 3 by exact_mod_cast hcard)
    nlinarith

end TaoTrudgianYang2025

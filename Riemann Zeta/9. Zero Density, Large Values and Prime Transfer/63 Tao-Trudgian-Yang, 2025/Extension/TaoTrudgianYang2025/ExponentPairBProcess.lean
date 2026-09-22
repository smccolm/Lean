import TaoTrudgianYang2025.BetaReflectionEnvelope
import TaoTrudgianYang2025.BetaClosedDuality

/-!
# The classical B-process for the paper's analytic exponent pairs

The transformed affine line is nonnegative throughout the closed unit
interval. The proved source reflection estimate therefore suffices;
no unproved exact beta-reflection identity is used.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem InExponentPairTriangle.bProcess {k l : ℝ}
    (h : InExponentPairTriangle k l) :
    InExponentPairTriangle (l-1/2) (k+1/2) := by
  rcases h with ⟨hk,hkhalf,hlhalf,hl,hkl⟩
  unfold InExponentPairTriangle
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem exponentPairLine_bProcess (k l α : ℝ) :
    exponentPairLine k l (1-α)+1/2-(1-α) =
      exponentPairLine (l-1/2) (k+1/2) α := by
  unfold exponentPairLine
  ring

theorem ExponentPair.bProcess {k l : ℝ} (h : ExponentPair k l) :
    ExponentPair (l-1/2) (k+1/2) := by
  apply (exponentPair_iff_beta_bound h.inTriangle.bProcess).mpr
  intro α hα
  have hαNN : α ≤ 1 := by exact_mod_cast hα
  let γ : ℝ≥0 := 1-α
  have hγreal : (γ : ℝ) = 1-(α : ℝ) := NNReal.coe_sub hαNN
  have hγ : (γ : ℝ) ≤ 1 := by
    rw [hγreal]
    linarith [α.coe_nonneg]
  have hγNN : γ ≤ 1 := by exact_mod_cast hγ
  have hdouble : (1-γ : ℝ≥0) = α := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hγNN,hγreal]
    norm_num
  have hline := exponentSumGrowthExponent_le_exponentPairLine_closed h γ hγ
  have hinput : IsExponentSumBoundNonAsymptotic γ (exponentPairLine k l γ) :=
    exponentSumGrowthExponent_le_iff_nonAsymptotic.mp hline
  have hnonneg : 0 ≤ exponentPairLine k l γ+1/2-(γ : ℝ) := by
    rw [hγreal,exponentPairLine_bProcess]
    have hk : 0 ≤ k := h.inTriangle.1
    have hl : l ≤ 1 := h.inTriangle.2.2.2.1
    have hlhalf : 1/2 ≤ l := h.inTriangle.2.2.1
    unfold exponentPairLine
    have hm : 0 ≤ (k+1/2-(l-1/2))*(α : ℝ) :=
      mul_nonneg (by linarith) α.coe_nonneg
    linarith
  have hout := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (isExponentSumBoundNonAsymptotic_reflect_nonnegative hγ hinput hnonneg)
  rw [hdouble,hγreal,exponentPairLine_bProcess] at hout
  exact hout

theorem exponentPair_bProcess_iff {k l : ℝ} :
    ExponentPair (l-1/2) (k+1/2) ↔ ExponentPair k l := by
  constructor
  · intro h
    convert h.bProcess using 1 <;> ring
  · exact ExponentPair.bProcess

end TaoTrudgianYang2025

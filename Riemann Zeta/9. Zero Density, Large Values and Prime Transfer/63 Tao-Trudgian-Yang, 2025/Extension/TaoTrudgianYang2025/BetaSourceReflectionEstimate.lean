import TaoTrudgianYang2025.BetaSourceMainBound

/-!
# Reflection estimate for the literal original exponential sum

The complete chart main bound is combined with the already proved
original-source stationary comparison. The short-interval branch uses
the actual empty retained set. All constants and model budgets precede
the original source data; no dual-window or extension premise remains.
-/

noncomputable section

open Set Expdb
open scoped NNReal BigOperators

namespace TaoTrudgianYang2025

theorem sourceExponentialSum_reflection_estimate
    {α : ℝ≥0} {β σ : ℝ}
    (hβ : IsExponentSumBoundNonAsymptotic α β) (hσ : 0 < σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 ∧
      ∃ P : ℕ, 2 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
          C ≤ T → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
          T^(1-(α : ℝ)-δ) ≤ N → N ≤ T^(1-(α : ℝ)+δ) →
          IsApproximateModelPhaseFunction F σ P δ →
          ‖exponentialSumAt F T N a b‖ ≤
            C*((N/Real.sqrt T)*T^(β+ε)+N/Real.sqrt T+T^ε) := by
  obtain ⟨δ,hd,hsmall,hpos,P,hP,C,hC,hmain⟩ :=
    sourceStationaryMain_physical_bound hβ hσ hε
  obtain ⟨D,hD,herror⟩ := modelPhase_source_sharp_comparison hσ hε
  let Q := max P bufferedLocalStationaryOrder
  let K := max C D
  have hK : 1 ≤ K := hC.trans (le_max_left _ _)
  refine ⟨δ,hd,hsmall,hpos,Q,hP.trans (le_max_left _ _),K,hK,?_⟩
  intro T N F a b hTK hN ha hb hlow hhigh hF
  have hT₁ : 1 ≤ T := hK.trans hTK
  have hT : 0 < T := zero_lt_one.trans_le hT₁
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let main := ∑ q ∈ modelPhaseSharpStationarySet F T N a b,
    modelPhaseStationaryMainTerm F T N q
  have hmainbound : ‖main‖ ≤ C*(N/Real.sqrt T)*T^(β+ε) := by
    by_cases hlong : (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N
    · exact hmain T N F a b ((le_max_left _ _).trans hTK) hNp ha hb hlow hhigh hlong
        (approximateModelPhase_mono hF (le_max_left _ _) le_rfl)
    · have hempty := modelPhaseSharpStationarySet_of_short (F := F) (le_of_not_gt hlong)
      dsimp only [main]
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have herr : ‖exponentialSumAt F T N a b-main‖ ≤ D*(N/Real.sqrt T+T^ε) :=
    herror N T a b hN hT₁ ha hb F δ hsmall
      (approximateModelPhase_mono hF (le_max_right _ _) le_rfl)
  have hX : 0 ≤ (N/Real.sqrt T)*T^(β+ε) := by positivity
  have hY : 0 ≤ N/Real.sqrt T+T^ε := by positivity
  calc
    ‖exponentialSumAt F T N a b‖ ≤ ‖exponentialSumAt F T N a b-main‖+‖main‖ :=
      by simpa only [add_comm] using norm_le_insert' (exponentialSumAt F T N a b) main
    _ ≤ D*(N/Real.sqrt T+T^ε)+C*(N/Real.sqrt T)*T^(β+ε) :=
      add_le_add herr hmainbound
    _ ≤ K*(N/Real.sqrt T+T^ε)+K*((N/Real.sqrt T)*T^(β+ε)) := by
      rw [mul_assoc C]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) hY)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
    _ = K*((N/Real.sqrt T)*T^(β+ε)+N/Real.sqrt T+T^ε) := by ring

end TaoTrudgianYang2025

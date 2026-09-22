import TaoTrudgianYang2025.BetaBufferedJets
import TaoTrudgianYang2025.BetaMorseWidthDegree

/-!
# Sharp uniform transformed-weight jets for varying buffered cutoffs

The constant precedes endpoints and width. The nth derivative costs
only eta^(-n), because inverse derivatives carry no transition-width loss.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def bufferedMorseDerivativeDegree (n : ℕ) : ℕ := n

theorem modelPhaseBufferedMorseWeight_uniform_derivative
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ v : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ (morseWeightDerivativeOrder n) δ →
        v ∈ modelPhaseSlopeRange F →
        ∀ z : ℝ,
          |iteratedDeriv n (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v) z| ≤
            C*(η⁻¹)^(bufferedMorseDerivativeDegree n) := by
  obtain ⟨M,hM,hcut⟩ := modelPhaseBufferedCutoff_uniform_ordered_jets (morseWeightCutoffOrder n)
  refine ⟨max (morseWeightDerivativeBound σ M n) 1,le_max_right _ _,?_⟩
  intro l r η hl hr hη hη₁ F δ v hδ hF hv z
  have hA : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
  have hs := modelPhaseBufferedCutoff_tsupport_model hη hl hr
  have hF₁ := approximateModelPhase_mono hF (morseWeightDerivativeOrder_pos n) le_rfl
  let B := morseWeightJetBudget σ M n
  have hsum : 0 ≤ ∑ k ∈ Finset.range (morseWeightCutoffOrder n+2),
      morseInverseDerivativeBound σ k :=
    Finset.sum_nonneg fun k _ => morseInverseDerivativeBound_nonneg hσ k
  have hB : 0 ≤ B := by
    dsimp [B,morseWeightJetBudget]
    linarith
  by_cases hz : z ∈ modelPhaseMorseRange F v
  · rw [iteratedDeriv_modelPhaseMorseWeight_eq hσ hδ hF₁ hv hz,
      iteratedDeriv_modelPhaseMorseAmplitude_formula (modelPhaseBufferedCutoff_contDiff l r η)
        hσ hδ hF₁ hv hz]
    have hjets : ∀ j ≤ morseWeightCutoffOrder n,
        |morseWeightJet (modelPhaseBufferedCutoff l r η) F v z j| ≤
          B*(η⁻¹)^(morseWeightWidthAtomDegree j) := by
      intro j hj
      by_cases he : j%2 = 0
      · simp only [morseWeightJet,morseWeightWidthAtomDegree,if_pos he]
        have hb := hcut l r η (modelPhaseMorseInverse F v z) hη (j/2) (by omega)
        exact hb.trans (mul_le_mul_of_nonneg_right
          (by dsimp [B,morseWeightJetBudget]; linarith)
          (pow_nonneg (inv_nonneg.mpr hη.le) _))
      · simp only [morseWeightJet,morseWeightWidthAtomDegree,if_neg he,pow_zero,mul_one]
        have hi := modelPhaseMorseInverse_iteratedDeriv_bound hσ hδ hF hv hz (j/2+1)
          (morseWeight_inverseOrder_le (by omega : j/2+1 ≤ morseWeightCutoffOrder n+1))
        have hb := Finset.single_le_sum (f := morseInverseDerivativeBound σ)
          (s := Finset.range (morseWeightCutoffOrder n+2))
          (fun k _ => morseInverseDerivativeBound_nonneg hσ k)
          (Finset.mem_range.mpr (by omega : j/2+1 < morseWeightCutoffOrder n+2))
        exact hi.trans (by dsimp [B,morseWeightJetBudget]; linarith)
    have h := inversePhaseEval_abs_le_weighted morseWeightWidthAtomDegree
      (morseWeightDerivativeExpression n) hB hA hjets
    apply h.trans
    change inversePhaseMagnitude _ B*(η⁻¹)^_ ≤ max (inversePhaseMagnitude _ B) 1*(η⁻¹)^n
    exact mul_le_mul (le_max_left _ _)
      (pow_le_pow_right₀ hA (morseWeightDerivativeExpression_widthDegree_le n))
      (pow_nonneg (inv_nonneg.mpr hη.le) _) (zero_le_one.trans (le_max_right _ _))
  · rw [iteratedDeriv_modelPhaseMorseWeight_zero hs hσ hδ hF₁ hv hz,abs_zero]
    positivity

end TaoTrudgianYang2025

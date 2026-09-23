import TaoTrudgianYang2025.SargosQuarticMorseWeightBounds
import TaoTrudgianYang2025.BetaBufferedJets
import TaoTrudgianYang2025.BetaMorseWidthDegree

/-! Cutoff-family bounds with the exact transition-width degree and uniform quantifier order. -/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticBufferedWeight_uniform_derivative (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (ε r : ℝ), |ε| ≤ 1/96 → r ∈ Icc 0 3 →
      ∀ z : ℝ,
        |iteratedDeriv n (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r) z| ≤
          C*(η⁻¹)^n := by
  obtain ⟨M,hM,hcut⟩ :=
    modelPhaseBufferedCutoff_uniform_ordered_jets (sargosQuarticMorseWeightCutoffOrder n)
  refine ⟨max (sargosQuarticMorseWeightDerivativeBound M n) 1,le_max_right _ _,?_⟩
  intro l b η hl hb hη hη₁ ε r hε hr z
  have hA : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
  have hs₁₂ := modelPhaseBufferedCutoff_tsupport_model hη hl hb
  have hs : tsupport (modelPhaseBufferedCutoff l b η) ⊆ Ioo (0 : ℝ) 3 := by
    intro u hu
    have h := hs₁₂ hu
    constructor <;> linarith [h.1,h.2]
  let B := sargosQuarticMorseWeightJetBudget M n
  have hsum : 0 ≤ ∑ k ∈ Finset.range (sargosQuarticMorseWeightCutoffOrder n+2),
      sargosQuarticMorseInverseDerivativeBound k :=
    Finset.sum_nonneg fun k _ => sargosQuarticMorseInverseDerivativeBound_nonneg k
  have hB : 0 ≤ B := by
    dsimp [B,sargosQuarticMorseWeightJetBudget]
    linarith
  by_cases hz : z ∈ sargosQuarticMorseRange ε r
  · rw [sargosQuarticMorseWeight_iteratedDeriv_eq hε hr hz,
      sargosQuarticMorseAmplitude_iteratedDeriv_formula
        (modelPhaseBufferedCutoff_contDiff l b η) hε hr hz]
    have hjets : ∀ j ≤ sargosQuarticMorseWeightCutoffOrder n,
        |sargosQuarticMorseWeightJet (modelPhaseBufferedCutoff l b η) ε r z j| ≤
          B*(η⁻¹)^(morseWeightWidthAtomDegree j) := by
      intro j hj
      by_cases he : j%2 = 0
      · simp only [sargosQuarticMorseWeightJet,morseWeightWidthAtomDegree,if_pos he]
        have h := hcut l b η (sargosQuarticMorseInverse ε r z) hη (j/2) (by omega)
        exact h.trans (mul_le_mul_of_nonneg_right
          (by dsimp [B,sargosQuarticMorseWeightJetBudget]; linarith)
          (pow_nonneg (inv_nonneg.mpr hη.le) _))
      · simp only [sargosQuarticMorseWeightJet,morseWeightWidthAtomDegree,if_neg he,pow_zero,mul_one]
        have hi := sargosQuarticMorseInverse_iteratedDeriv_bound hε hr hz (j/2+1)
        have h := Finset.single_le_sum (f := sargosQuarticMorseInverseDerivativeBound)
          (s := Finset.range (sargosQuarticMorseWeightCutoffOrder n+2))
          (fun k _ => sargosQuarticMorseInverseDerivativeBound_nonneg k)
          (Finset.mem_range.mpr (by omega : j/2+1 < sargosQuarticMorseWeightCutoffOrder n+2))
        exact hi.trans (by dsimp [B,sargosQuarticMorseWeightJetBudget]; linarith)
    have h := inversePhaseEval_abs_le_weighted morseWeightWidthAtomDegree
      (morseWeightDerivativeExpression n) hB hA hjets
    apply h.trans
    change inversePhaseMagnitude _ B*(η⁻¹)^_ ≤ max (inversePhaseMagnitude _ B) 1*(η⁻¹)^n
    exact mul_le_mul (le_max_left _ _)
      (pow_le_pow_right₀ hA (morseWeightDerivativeExpression_widthDegree_le n))
      (pow_nonneg (inv_nonneg.mpr hη.le) _) (zero_le_one.trans (le_max_right _ _))
  · rw [sargosQuarticMorseWeight_iteratedDeriv_zero hs hε hr hz,abs_zero]
    positivity

end TaoTrudgianYang2025


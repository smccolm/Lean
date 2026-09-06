import GafniTao.Pintz2023Equation420Residue
import GafniTao.Pintz2023PoweredScaleUpper

/-!
# Pintz (2023), complete equation (4.20) Gram bound

This module absorbs the moving-pole residue and exposes the single decaying
Gram bound used in the large-local-frequency branch of equation (4.19).
-/

open Complex

namespace GafniTao

noncomputable section

/-- Complete energy-weighted equation-(4.20) estimate, with the critical,
local-frequency, block-upper, and selected-zero separation hypotheses all
visible. -/
theorem exists_pintz2023_equation420_gram_native
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (etaJ etaK gamma delta T : ℝ),
      0 < N → etaJ ∈ Set.Icc 0 eta → etaK ∈ Set.Icc 0 eta →
      1 ≤ |delta - gamma| → 1 ≤ T →
      T ^ pintz2023EllThreshold eta data.epsilon ell ≤ (N : ℝ) →
      |delta - gamma| ^ (19 / (10 * (ell : ℝ))) ≤ (N : ℝ) →
      (N : ℝ) ≤ T ^ (3 : ℝ) →
      3 * pintz2023SourceLambda T k ≤ |delta - gamma| →
      (N : ℝ) ^ (-4 * eta) *
          ‖pintz2023SmoothedZetaSum N
            (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
              I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
        C * (4 * eta)⁻¹ *
          ((4 ^ pintz2023NearOneGramExponent
              eta eta data.epsilon + 3) *
            T ^ (-data.epsilon / (k : ℝ))) := by
  obtain ⟨C, hC, hGram⟩ :=
    exists_pintz2023_equation420_weighted_gram_native hcell data
  refine ⟨C, hC, ?_⟩
  intro N etaJ etaK gamma delta T hN hetaJ hetaK hSep hT
    hCritical hFrequency hNUpper hSelectedSep
  have hRaw := hGram N etaJ etaK gamma delta T hN hetaJ hetaK
    hSep hT hCritical hFrequency
  have hResidue := pintz2023_equation420_residue_decay hcell data hT
    hNUpper hSelectedSep
  have hFactorNonneg : 0 ≤ C * (4 * eta)⁻¹ := by
    have heta : 0 < eta := pintzCell_eta_pos hcell
    positivity
  calc
    (N : ℝ) ^ (-4 * eta) *
          ‖pintz2023SmoothedZetaSum N
            (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
              I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
        C * (4 * eta)⁻¹ *
          (4 ^ pintz2023NearOneGramExponent eta eta data.epsilon *
              T ^ (-data.epsilon / (k : ℝ)) +
            (N : ℝ) ^ (2 * eta) * (|delta - gamma| + 2) *
              Real.exp (-(Real.pi * |delta - gamma|) / 2)) := hRaw
    _ ≤ C * (4 * eta)⁻¹ *
        (4 ^ pintz2023NearOneGramExponent eta eta data.epsilon *
            T ^ (-data.epsilon / (k : ℝ)) +
          3 * T ^ (-data.epsilon / (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right hResidue _) hFactorNonneg
    _ = C * (4 * eta)⁻¹ *
          ((4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) *
            T ^ (-data.epsilon / (k : ℝ))) := by ring_nf

#print axioms exists_pintz2023_equation420_gram_native

end

end GafniTao

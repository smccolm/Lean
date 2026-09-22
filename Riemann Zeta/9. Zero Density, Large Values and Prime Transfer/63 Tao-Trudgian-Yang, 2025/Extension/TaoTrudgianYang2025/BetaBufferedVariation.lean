import TaoTrudgianYang2025.BetaBufferedCutoff
import TaoTrudgianYang2025.BetaAmplitudeVariation
import TaoTrudgianYang2025.AtkinsonResidualVariation

/-!
# Width-independent variation of the actual cutoff-weighted amplitude

The generic two-transition variation theorem is applied to the literal
buffered cutoff. Sampling uses the actual antitone inverse slope.
No plateau hypothesis is imposed on this original source cutoff.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025

theorem modelPhaseBufferedCutoff_eq_band {η : ℝ} (hη : 0 < η) (l r u : ℝ) :
    modelPhaseBufferedCutoff l r η u =
      zetaBandCutoff (l+η) (l+2*η) (r-2*η) (r-η) u := by
  unfold modelPhaseBufferedCutoff zetaBandCutoff
  rw [show l+2*η-(l+η) = η by ring,show r-η-(r-2*η) = η by ring]
  congr 2 <;> field_simp [hη.ne'] <;> ring

theorem finiteVariationBound_modelPhaseBufferedCutoff_sample
    {η : ℝ} (hη : 0 < η) (l r : ℝ) (u : ℕ → ℝ) (L : ℕ)
    (hu : MonotoneOn u (Iic L) ∨ AntitoneOn u (Iic L)) :
    FiniteVariationBound (fun i => (modelPhaseBufferedCutoff l r η (u i) : ℂ)) L 2 := by
  have h := finiteVariationBound_zetaBandCutoff_sample
    (show l+η < l+2*η by linarith) (show r-2*η < r-η by linarith) u L hu
  exact h.congr (fun i _ => by rw [modelPhaseBufferedCutoff_eq_band hη])

theorem finiteVariationBound_modelPhaseBufferedCutoff_inverse
    {σ δ T N η : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (l r a : ℝ) (L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → (a+i)*N/T ∈ modelPhaseSlopeRange F) :
    FiniteVariationBound
      (fun i => (modelPhaseBufferedCutoff l r η
        (modelPhaseInverseSlope F ((a+i)*N/T)) : ℂ)) L 2 := by
  apply finiteVariationBound_modelPhaseBufferedCutoff_sample hη
  right
  intro i hi j hj hij
  apply modelPhaseInverseSlope_antitoneOn hσ hδ hF (hv i hi) (hv j hj)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (show (i : ℝ) ≤ j by exact_mod_cast hij)) hN.le) hT.le

theorem finiteVariationBound_modelPhaseBufferedAmplitude
    {σ δ T N η : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (l r a : ℝ) (L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → (a+i)*N/T ∈ modelPhaseSlopeRange F) :
    FiniteVariationBound
      (fun i => (modelPhaseBufferedCutoff l r η
        (modelPhaseInverseSlope F ((a+i)*N/T)) : ℂ)*
          (modelPhasePhysicalAmplitude F T N (a+i) : ℂ)) L
      (4*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹)) := by
  have hc := finiteVariationBound_modelPhaseBufferedCutoff_inverse hσ
    (hδ.trans (min_le_left _ _))
    (approximateModelPhase_mono hF (by norm_num : 1 ≤ 2) le_rfl)
    hT hN hη l r a L hv
  have ha := finiteVariationBound_modelPhasePhysicalAmplitude hσ hδ hF hT hN a L hv
  convert hc.mul ha using 1
  ring

end TaoTrudgianYang2025

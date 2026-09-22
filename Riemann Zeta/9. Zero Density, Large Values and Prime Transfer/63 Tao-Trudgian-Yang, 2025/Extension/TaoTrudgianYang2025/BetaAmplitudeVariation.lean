import TaoTrudgianYang2025.BetaAmplitudeMonotonicity
import TaoTrudgianYang2025.FiniteWeightVariation

/-!
# Uniform variation of the actual physical stationary amplitude

The weight uses the second derivative of the original physical phase.
Its bound is N/sqrt(T) times a constant depending only on sigma.
The finite variation covers exactly the sampled indices, with no
extra point outside the actual slope image.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

def modelPhasePhysicalAmplitude (F : ℝ → ℝ) (T N r : ℝ) : ℝ :=
  (Real.sqrt (-deriv (deriv (modelPhaseFrequencyPhase F T N r))
    (modelPhaseStationaryPoint F T N r)))⁻¹

theorem modelPhasePhysicalAmplitude_eq
    {σ δ T N r : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhasePhysicalAmplitude F T N r =
      (N/Real.sqrt T)*modelPhaseStationaryAmplitude F (r*N/T) :=
  modelPhaseStationaryPoint_amplitude_scale hF hT hN hv

theorem modelPhasePhysicalAmplitude_pos
    {σ δ T N r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    0 < modelPhasePhysicalAmplitude F T N r := by
  rw [modelPhasePhysicalAmplitude_eq hF hT hN hv]
  exact mul_pos (div_pos hN (Real.sqrt_pos.mpr hT))
    (modelPhaseStationaryAmplitude_pos hσ hδ hF hv)

theorem modelPhasePhysicalAmplitude_le
    {σ δ T N r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhasePhysicalAmplitude F T N r ≤
      (N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹ := by
  rw [modelPhasePhysicalAmplitude_eq hF hT hN hv]
  exact mul_le_mul_of_nonneg_left (modelPhaseStationaryAmplitude_bounds hσ hδ hF hv).2
    (by positivity)

theorem modelPhasePhysicalAmplitude_antitoneOn
    {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hN : 0 < N) :
    AntitoneOn (modelPhasePhysicalAmplitude F T N)
      {r : ℝ | r*N/T ∈ modelPhaseSlopeRange F} := by
  intro r hr s hs hrs
  rw [modelPhasePhysicalAmplitude_eq hF hT hN hr,
    modelPhasePhysicalAmplitude_eq hF hT hN hs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply modelPhaseStationaryAmplitude_antitoneOn hσ hδ hF hr hs
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrs hN.le) hT.le

theorem finiteVariationBound_modelPhasePhysicalAmplitude
    {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hN : 0 < N) (a : ℝ) (L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → (a+i)*N/T ∈ modelPhaseSlopeRange F) :
    FiniteVariationBound (fun i => (modelPhasePhysicalAmplitude F T N (a+i) : ℂ)) L
      ((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) := by
  have hd : δ ≤ min (modelPhaseCurvatureLower σ) 1 := hδ.trans (min_le_left _ _)
  have hF₁ := approximateModelPhase_mono hF (by norm_num : 1 ≤ 2) le_rfl
  apply finiteVariationBound_of_antitone (by positivity)
  · intro i hi j hj hij
    apply modelPhasePhysicalAmplitude_antitoneOn hσ hδ hF hT hN (hv i hi) (hv j hj)
    exact add_le_add le_rfl (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij)
  · intro i hi
    exact ⟨(modelPhasePhysicalAmplitude_pos hσ hd hF₁ hT hN (hv i hi)).le,
      modelPhasePhysicalAmplitude_le hσ hd hF₁ hT hN (hv i hi)⟩

theorem norm_sum_range_succ_mul_le_of_finiteVariation
    {w z : ℕ → ℂ} {L : ℕ} {M B : ℝ}
    (hw : FiniteVariationBound w L M) (hB : 0 ≤ B)
    (hz : ∀ j ≤ L+1, ‖∑ i ∈ Finset.range j, z i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (L+1), w i*z i‖ ≤ 2*M*B := by
  have h := norm_sum_mul_le_discrete_parts w z (L+1)
  simp only [Nat.add_sub_cancel] at h
  apply h.trans
  have he := mul_le_mul (hw.norm_le L le_rfl) (hz (L+1) le_rfl)
    (norm_nonneg _) hw.nonneg
  have hs : (∑ i ∈ Finset.range L,
      ‖w (i+1)-w i‖*‖∑ k ∈ Finset.range (i+1), z k‖) ≤ M*B := by
    calc
      _ ≤ ∑ i ∈ Finset.range L, ‖w (i+1)-w i‖*B := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hz (i+1) (by
          have := Finset.mem_range.mp hi
          omega)) (norm_nonneg _)
      _ = (∑ i ∈ Finset.range L, ‖w (i+1)-w i‖)*B := (Finset.sum_mul _ _ _).symm
      _ ≤ M*B := mul_le_mul_of_nonneg_right hw.variation_le hB
  nlinarith

end TaoTrudgianYang2025

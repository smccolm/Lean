import TaoTrudgianYang2025.BetaMorseMonotonicity

/-!
# The actual smooth inverse of the quadratic coordinate

The inverse is restricted to the coordinate image of (1,2).
Its identities, smoothness and critical Jacobian are proved from the
original model phase and the positive coordinate derivative.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def modelPhaseMorseRange (F : ℝ → ℝ) (v : ℝ) : Set ℝ :=
  modelPhaseMorseCoordinate F v '' Ioo (1 : ℝ) 2

def modelPhaseMorseInverse (F : ℝ → ℝ) (v : ℝ) : ℝ → ℝ :=
  Function.invFunOn (modelPhaseMorseCoordinate F v) (Ioo (1 : ℝ) 2)

theorem modelPhaseMorseInverse_mem {F : ℝ → ℝ} {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseInverse F v z ∈ Ioo (1 : ℝ) 2 :=
  Function.invFunOn_mem hz

theorem modelPhaseMorseCoordinate_inverse {F : ℝ → ℝ} {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseCoordinate F v (modelPhaseMorseInverse F v z) = z :=
  Function.invFunOn_eq hz

theorem modelPhaseMorseInverse_coordinate
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseMorseInverse F v (modelPhaseMorseCoordinate F v u) = u :=
  (modelPhaseMorseCoordinate_strictMonoOn hσ hδ hF hv).injOn.leftInvOn_invFunOn hu

theorem zero_mem_modelPhaseMorseRange {F : ℝ → ℝ} {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange F) :
    0 ∈ modelPhaseMorseRange F v :=
  ⟨modelPhaseInverseSlope F v,modelPhaseInverseSlope_mem hv,
    modelPhaseMorseCoordinate_at_inverse F v⟩

theorem modelPhaseMorseInverse_zero
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseInverse F v 0 = modelPhaseInverseSlope F v := by
  simpa only [modelPhaseMorseCoordinate_at_inverse] using
    modelPhaseMorseInverse_coordinate hσ hδ hF hv (modelPhaseInverseSlope_mem hv)

theorem modelPhaseMorseInverse_hasStrictDerivAt
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    HasStrictDerivAt (modelPhaseMorseInverse F v)
      (deriv (modelPhaseMorseCoordinate F v) (modelPhaseMorseInverse F v z))⁻¹ z := by
  rcases hz with ⟨u,hu,rfl⟩
  rw [modelPhaseMorseInverse_coordinate hσ hδ hF hv hu]
  have hd := (modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  apply hd.to_local_left_inverse (modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv hu).ne'
  filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
  exact modelPhaseMorseInverse_coordinate hσ hδ hF hv hx

theorem modelPhaseMorseRange_isOpen
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    IsOpen (modelPhaseMorseRange F v) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨u,hu,rfl⟩
  have hd := (modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hi := Filter.image_mem_map (m := modelPhaseMorseCoordinate F v) (isOpen_Ioo.mem_nhds hu)
  rwa [hd.map_nhds_eq (modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv hu).ne'] at hi

theorem modelPhaseMorseInverse_contDiffAt
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    ContDiffAt ℝ ∞ (modelPhaseMorseInverse F v) z := by
  rcases hz with ⟨u,hu,rfl⟩
  have hc := modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu
  have hd := hc.hasStrictDerivAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have he := hd.hasStrictFDerivAt_equiv (modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv hu).ne'
  have hg : ∀ᶠ x in 𝓝 u,
      modelPhaseMorseInverse F v (modelPhaseMorseCoordinate F v x) = x := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact modelPhaseMorseInverse_coordinate hσ hδ hF hv hx
  exact (hc.to_localInverse he.hasFDerivAt (by simp)).congr_of_eventuallyEq
    (he.localInverse_unique hg)

theorem modelPhaseMorseInverse_hasDerivAt_zero
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseMorseInverse F v) (modelPhaseStationaryAmplitude F v) 0 := by
  have h := (modelPhaseMorseInverse_hasStrictDerivAt hσ hδ hF hv
    (zero_mem_modelPhaseMorseRange hv)).hasDerivAt
  rwa [modelPhaseMorseInverse_zero hσ hδ hF hv,
    modelPhaseMorseCoordinate_reciprocal_derivative_amplitude hF hv] at h

theorem modelPhaseMorseInverse_quadratic
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    F (modelPhaseMorseInverse F v z)-v*modelPhaseMorseInverse F v z =
      -modelPhaseLegendreDual F v-z^2/2 := by
  simpa only [modelPhaseMorseCoordinate_inverse hz] using
    modelPhaseMorseCoordinate_normalForm hσ hδ hF hv (modelPhaseMorseInverse_mem hz)

theorem modelPhaseFrequencyPhase_morseInverse
    {F : ℝ → ℝ} {σ δ T N r z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : r*N/T ∈ modelPhaseSlopeRange F)
    (hz : z ∈ modelPhaseMorseRange F (r*N/T)) :
    modelPhaseFrequencyPhase F T N r (N*modelPhaseMorseInverse F (r*N/T) z) =
      modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) -(T/2)*z^2 := by
  have hx : (N*modelPhaseMorseInverse F (r*N/T) z)/N =
      modelPhaseMorseInverse F (r*N/T) z := mul_div_cancel_left₀ _ hN
  have h := modelPhaseFrequencyPhase_quadratic_normalForm hσ hδ hF hT hN hv
    (hx.symm ▸ modelPhaseMorseInverse_mem hz)
  simpa only [hx,modelPhaseMorseCoordinate_inverse hz] using h

end TaoTrudgianYang2025


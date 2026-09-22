import TaoTrudgianYang2025.BetaSlopeInverse

/-!
# The genuine closed-interval slope and exact stationary range

At the original endpoints the derivative is taken within [1,2].
This does not impose any regularity on the irrelevant exterior extension of F.
On the open interval it equals the ordinary derivative used by the actual
Fourier modes and inverse slope.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

def modelPhaseClosedSlope (F : ℝ → ℝ) : ℝ → ℝ :=
  derivWithin F phaseInterval

theorem modelPhaseClosedSlope_eq_deriv {F : ℝ → ℝ} {u : ℝ}
    (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F u = deriv F u :=
  derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)

theorem modelPhaseClosedSlope_eventuallyEq_deriv {F : ℝ → ℝ} {u : ℝ}
    (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F =ᶠ[𝓝 u] deriv F := by
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact modelPhaseClosedSlope_eq_deriv hv

theorem modelPhaseClosedSlope_continuousOn {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) :
    ContinuousOn (modelPhaseClosedSlope F) (Icc (1 : ℝ) 2) :=
  hF.1.continuousOn_derivWithin uniqueDiffOn_phaseInterval (by simp)

theorem modelPhaseClosedSlope_drop {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u v : ℝ} (hu : u ∈ Icc (1 : ℝ) 2) (hv : v ∈ Icc (1 : ℝ) 2)
    (huv : u ≤ v) :
    modelPhaseCurvatureLower σ*(v-u) ≤ modelPhaseClosedSlope F u-modelPhaseClosedSlope F v := by
  have hd : DifferentiableOn ℝ (modelPhaseClosedSlope F) (interior (Icc (1 : ℝ) 2)) := by
    intro x hx
    have hx' : x ∈ Ioo (1 : ℝ) 2 := by simpa only [interior_Icc] using hx
    exact (((approximateModelPhase_deriv_contDiffAt hF hx').differentiableAt (by simp)).congr_of_eventuallyEq (modelPhaseClosedSlope_eventuallyEq_deriv hx')).differentiableWithinAt
  have hb : ∀ x ∈ interior (Icc (1 : ℝ) 2),
      deriv (modelPhaseClosedSlope F) x ≤ -modelPhaseCurvatureLower σ := by
    intro x hx
    have hx' : x ∈ Ioo (1 : ℝ) 2 := by simpa only [interior_Icc] using hx
    rw [(modelPhaseClosedSlope_eventuallyEq_deriv hx').deriv_eq]
    have h := (approximateModelPhase_curvature_deriv_bounds hσ hδ hF hx').1
    linarith
  have h := (convex_Icc (1 : ℝ) 2).image_sub_le_mul_sub_of_deriv_le
    (modelPhaseClosedSlope_continuousOn hF) hd hb u hu v hv huv
  linarith

theorem modelPhaseClosedSlope_strictAntiOn {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    StrictAntiOn (modelPhaseClosedSlope F) (Icc (1 : ℝ) 2) := by
  intro u hu v hv huv
  have hd := modelPhaseClosedSlope_drop hσ hδ hF hu hv huv.le
  have hp := mul_pos (modelPhaseCurvatureLower_pos hσ) (sub_pos.mpr huv)
  linarith

theorem modelPhaseSlopeRange_eq_endpoint_Ioo {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    modelPhaseSlopeRange F = Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1) := by
  have hm := modelPhaseClosedSlope_strictAntiOn hσ hδ hF
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    rw [← modelPhaseClosedSlope_eq_deriv hu]
    exact ⟨hm ⟨hu.1.le,hu.2.le⟩ (by norm_num) hu.2,
      hm (by norm_num) ⟨hu.1.le,hu.2.le⟩ hu.1⟩
  · intro hv
    obtain ⟨u,hu,he⟩ := intermediate_value_Ioo' (by norm_num : (1 : ℝ) ≤ 2)
      (modelPhaseClosedSlope_continuousOn hF) hv
    exact ⟨u,hu,(modelPhaseClosedSlope_eq_deriv hu).symm.trans he⟩

theorem modelPhaseClosedSlope_model_error {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    |modelPhaseClosedSlope F u-u^(-σ)| ≤ δ := by
  have he := hF.2 0 (Nat.zero_le P) ⟨u,hu⟩
  change ‖iteratedDerivWithin 1 F phaseInterval u-modelPhase σ u‖ ≤ δ at he
  simpa only [iteratedDerivWithin_one,modelPhaseClosedSlope,modelPhase,Real.norm_eq_abs] using he

theorem modelPhaseClosedSlope_deriv_bounds {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F 2 ≤ deriv F u ∧ deriv F u ≤ modelPhaseClosedSlope F 1 := by
  have hm := (modelPhaseClosedSlope_strictAntiOn hσ hδ hF).antitoneOn
  rw [← modelPhaseClosedSlope_eq_deriv hu]
  exact ⟨hm ⟨hu.1.le,hu.2.le⟩ (by norm_num) hu.2.le,
    hm (by norm_num) ⟨hu.1.le,hu.2.le⟩ hu.1.le⟩

end TaoTrudgianYang2025

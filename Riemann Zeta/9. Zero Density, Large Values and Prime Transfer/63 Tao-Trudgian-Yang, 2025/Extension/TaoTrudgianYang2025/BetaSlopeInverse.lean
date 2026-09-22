import TaoTrudgianYang2025.BetaSecondDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Inverting the derivative of an actual approximate model phase

All inverse identities are restricted to the derivative image of (1,2).
No global derivative at the endpoints, nor any dual exponential-sum estimate,
is assumed. The small-error model hypothesis supplies strict negative curvature.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

def modelPhaseSlopeRange (F : ℝ → ℝ) : Set ℝ :=
  deriv F '' Ioo (1 : ℝ) 2

def modelPhaseInverseSlope (F : ℝ → ℝ) : ℝ → ℝ :=
  Function.invFunOn (deriv F) (Ioo (1 : ℝ) 2)

theorem approximateModelPhase_contDiffAt {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ F u :=
  hF.1.contDiffAt (Icc_mem_nhds hu.1 hu.2)

theorem approximateModelPhase_deriv_contDiffAt {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ (deriv F) u := by
  exact (approximateModelPhase_contDiffAt hF hu).derivWithin (by simp)

theorem approximateModelPhase_deriv_strictAntiOn {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    StrictAntiOn (deriv F) (Ioo (1 : ℝ) 2) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 1 2)
  · exact fun u hu =>
      (approximateModelPhase_deriv_contDiffAt hF hu).continuousAt.continuousWithinAt
  · intro u hu
    have hui : u ∈ Ioo (1 : ℝ) 2 := by simpa using hu
    have hb := (approximateModelPhase_curvature_deriv_bounds hσ hδ hF hui).1
    have hp := modelPhaseCurvatureLower_pos hσ
    linarith

theorem modelPhaseInverseSlope_mem {F : ℝ → ℝ} {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseInverseSlope F v ∈ Ioo (1 : ℝ) 2 :=
  Function.invFunOn_mem hv

theorem deriv_modelPhaseInverseSlope_apply {F : ℝ → ℝ} {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange F) :
    deriv F (modelPhaseInverseSlope F v) = v :=
  Function.invFunOn_eq hv

theorem modelPhaseInverseSlope_deriv {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseInverseSlope F (deriv F u) = u :=
  (approximateModelPhase_deriv_strictAntiOn hσ hδ hF).injOn.leftInvOn_invFunOn hu

theorem approximateModelPhase_secondDeriv_ne_zero {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    deriv (deriv F) u ≠ 0 := by
  have hb := (approximateModelPhase_curvature_deriv_bounds hσ hδ hF hu).1
  have hp := modelPhaseCurvatureLower_pos hσ
  linarith

theorem modelPhaseInverseSlope_hasStrictDerivAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasStrictDerivAt (modelPhaseInverseSlope F)
      (deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹ v := by
  rcases hv with ⟨u, hu, rfl⟩
  rw [modelPhaseInverseSlope_deriv hσ hδ hF hu]
  have hd := (approximateModelPhase_deriv_contDiffAt hF hu).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  apply hd.to_local_left_inverse (approximateModelPhase_secondDeriv_ne_zero hσ hδ hF hu)
  filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
  exact modelPhaseInverseSlope_deriv hσ hδ hF hx

theorem modelPhaseSlopeRange_contains_interval {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (hb : b < 2) :
    Ioo (deriv F b) (deriv F a) ⊆ modelPhaseSlopeRange F := by
  have hc : ContinuousOn (deriv F) (Icc a b) := by
    intro u hu
    exact (approximateModelPhase_deriv_contDiffAt hF
      ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩).continuousAt.continuousWithinAt
  intro v hv
  rcases intermediate_value_Ioo' hab hc hv with ⟨u, hu, hval⟩
  exact ⟨u, ⟨ha.trans hu.1, hu.2.trans hb⟩, hval⟩

theorem modelPhaseSlopeRange_isOpen {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    IsOpen (modelPhaseSlopeRange F) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro v ⟨u, hu, rfl⟩
  have hd := (approximateModelPhase_deriv_contDiffAt hF hu).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hi := Filter.image_mem_map (m := deriv F) (isOpen_Ioo.mem_nhds hu)
  rwa [hd.map_nhds_eq (approximateModelPhase_secondDeriv_ne_zero hσ hδ hF hu)] at hi

theorem modelPhaseInverseSlope_contDiffAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseInverseSlope F) v := by
  rcases hv with ⟨u, hu, rfl⟩
  have hc := approximateModelPhase_deriv_contDiffAt hF hu
  have hd := hc.hasStrictDerivAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have he := hd.hasStrictFDerivAt_equiv
    (approximateModelPhase_secondDeriv_ne_zero hσ hδ hF hu)
  have hg : ∀ᶠ x in 𝓝 u, modelPhaseInverseSlope F (deriv F x) = x := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact modelPhaseInverseSlope_deriv hσ hδ hF hx
  exact (hc.to_localInverse he.hasFDerivAt (by simp)).congr_of_eventuallyEq
    (he.localInverse_unique hg)

end TaoTrudgianYang2025

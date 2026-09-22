import TaoTrudgianYang2025.BetaMorseRemainder

/-!
# Smooth zero-extension of the actual transformed source weight

The original cutoff has compact support strictly inside the source interval.
Its image under the actual smooth coordinate is compact inside the Morse
image. This proves smooth extension by zero, including at the moving boundary.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def modelPhaseMorseWeight (χ F : ℝ → ℝ) (v : ℝ) : ℝ → ℝ :=
  (modelPhaseMorseRange F v).indicator (modelPhaseMorseAmplitude χ F v)

theorem modelPhaseMorseWeight_eq {χ F : ℝ → ℝ} {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseWeight χ F v z = modelPhaseMorseAmplitude χ F v z :=
  Set.indicator_of_mem hz _

theorem modelPhaseMorseWeight_zero_of_not_mem {χ F : ℝ → ℝ} {v z : ℝ}
    (hz : z ∉ modelPhaseMorseRange F v) :
    modelPhaseMorseWeight χ F v z = 0 :=
  Set.indicator_of_notMem hz _

theorem modelPhaseMorseWeight_support_subset {χ F : ℝ → ℝ} {v : ℝ} :
    Function.support (modelPhaseMorseWeight χ F v) ⊆
      modelPhaseMorseCoordinate F v '' tsupport χ := by
  intro z hz
  have hr : z ∈ modelPhaseMorseRange F v := by
    by_contra hn
    exact hz (modelPhaseMorseWeight_zero_of_not_mem hn)
  refine ⟨modelPhaseMorseInverse F v z,?_,modelPhaseMorseCoordinate_inverse hr⟩
  apply subset_tsupport χ
  intro hc
  apply hz
  rw [modelPhaseMorseWeight_eq hr,modelPhaseMorseAmplitude,hc,zero_mul]

theorem isCompact_modelPhaseMorseCoordinate_image_tsupport
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    IsCompact (modelPhaseMorseCoordinate F v '' tsupport χ) := by
  have hc : IsCompact (tsupport χ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) (hs.trans Ioo_subset_Icc_self)
  exact hc.image_of_continuousOn
    ((modelPhaseMorseCoordinate_contDiffOn hσ hδ hF hv).continuousOn.mono hs)

theorem modelPhaseMorseWeight_tsupport_subset
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    tsupport (modelPhaseMorseWeight χ F v) ⊆
      modelPhaseMorseCoordinate F v '' tsupport χ :=
  closure_minimal modelPhaseMorseWeight_support_subset
    (isCompact_modelPhaseMorseCoordinate_image_tsupport hs hσ hδ hF hv).isClosed

theorem modelPhaseMorseWeight_tsupport_subset_range
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    tsupport (modelPhaseMorseWeight χ F v) ⊆ modelPhaseMorseRange F v :=
  (modelPhaseMorseWeight_tsupport_subset hs hσ hδ hF hv).trans (image_mono hs)

theorem modelPhaseMorseWeight_contDiff
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiff ℝ ∞ (modelPhaseMorseWeight χ F v) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ modelPhaseMorseRange F v
  · apply (modelPhaseMorseAmplitude_contDiffAt hχ hσ hδ hF hv hz).congr_of_eventuallyEq
    filter_upwards [(modelPhaseMorseRange_isOpen hσ hδ hF hv).mem_nhds hz] with u hu
    exact modelPhaseMorseWeight_eq hu
  · have hn : z ∉ tsupport (modelPhaseMorseWeight χ F v) :=
      fun h => hz (modelPhaseMorseWeight_tsupport_subset_range hs hσ hδ hF hv h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem modelPhaseMorseWeight_hasCompactSupport
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    HasCompactSupport (modelPhaseMorseWeight χ F v) :=
  (isCompact_modelPhaseMorseCoordinate_image_tsupport hs hσ hδ hF hv).of_isClosed_subset
    (isClosed_tsupport _) (modelPhaseMorseWeight_tsupport_subset hs hσ hδ hF hv)

theorem modelPhaseMorseWeight_zero
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseWeight χ F v 0 =
      χ (modelPhaseInverseSlope F v)*modelPhaseStationaryAmplitude F v := by
  rw [modelPhaseMorseWeight_eq (zero_mem_modelPhaseMorseRange hv),
    modelPhaseMorseAmplitude_zero hσ hδ hF hv]

theorem modelPhaseMorseWeight_tsupport_uniform
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    tsupport (modelPhaseMorseWeight χ F v) ⊆
      Icc (-Real.sqrt (σ+1)) (Real.sqrt (σ+1)) := by
  intro z hz
  rcases modelPhaseMorseWeight_tsupport_subset hs hσ hδ hF hv hz with ⟨u,hu,rfl⟩
  have hg := modelPhaseInverseSlope_mem hv
  have hd : |u-modelPhaseInverseSlope F v| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [(hs hu).1,(hs hu).2,hg.1,hg.2]
  have hb := (modelPhaseMorseCoordinate_bounds hσ hδ hF hv (hs hu)).2
  have h := hb.trans (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg (σ+1)))
  simpa only [mul_one,abs_le] using h

end TaoTrudgianYang2025

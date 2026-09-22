import TaoTrudgianYang2025.BetaCurvatureAmplitude

/-!
# Source third-derivative sign and monotone stationary amplitudes

The reference third derivative is uniformly positive on [1,2].
A fixed positive tolerance depending only on sigma preserves this sign.
The actual inverse slope then gives an antitone curvature amplitude.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def modelPhaseThirdLower (σ : ℝ) : ℝ :=
  σ*(σ+1)*2^(-σ-2)/2

def modelPhaseAmplitudeTolerance (σ : ℝ) : ℝ :=
  min (min (modelPhaseCurvatureLower σ) 1) (min (modelPhaseThirdLower σ) 1)

theorem modelPhaseThirdLower_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseThirdLower σ := by
  unfold modelPhaseThirdLower
  positivity

theorem modelPhaseAmplitudeTolerance_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseAmplitudeTolerance σ :=
  lt_min (lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one)
    (lt_min (modelPhaseThirdLower_pos hσ) zero_lt_one)

theorem approximateModelPhase_thirdWithin_bounds
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    modelPhaseThirdLower σ ≤ iteratedDerivWithin 3 F phaseInterval u ∧
      iteratedDerivWithin 3 F phaseInterval u ≤ σ*(σ+1)+1 := by
  have he := hF.2 2 le_rfl ⟨u,hu⟩
  rw [modelPhaseErrorAt,iteratedDerivWithin_modelPhase σ 2 hu] at he
  norm_num at he
  have hcoeff : (descPochhammer ℝ 2).eval (-σ) = σ*(σ+1) := by
    norm_num [descPochhammer_succ_eval]
    ring
  rw [hcoeff] at he
  have he' := he
  have huPos : 0 < u := zero_lt_one.trans_le hu.1
  have hlow : (2 : ℝ)^(-σ-2) ≤ u^(-σ-2) :=
    Real.rpow_le_rpow_of_nonpos huPos hu.2 (by linarith)
  have hhigh : u^(-σ-2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu.1 (by linarith)
  have hc : 0 ≤ σ*(σ+1) := by positivity
  have hl := mul_le_mul_of_nonneg_left hlow hc
  have hh := mul_le_mul_of_nonneg_left hhigh hc
  have hd₀ := hδ.trans (min_le_left _ _)
  have hd₁ := hδ.trans (min_le_right _ _)
  rw [abs_le] at he'
  unfold modelPhaseThirdLower at hd₀ ⊢
  constructor <;> nlinarith

theorem approximateModelPhase_thirdDeriv_bounds
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseThirdLower σ ≤ deriv (deriv (deriv F)) u ∧
      deriv (deriv (deriv F)) u ≤ σ*(σ+1)+1 := by
  have hc : ContDiffAt ℝ 3 F u :=
    (approximateModelPhase_contDiffAt hF hu).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have h := approximateModelPhase_thirdWithin_bounds hσ hδ hF ⟨hu.1.le,hu.2.le⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hc
    ⟨hu.1.le,hu.2.le⟩] at h
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using h

theorem approximateModelPhase_secondDeriv_strictMonoOn
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ) :
    StrictMonoOn (deriv (deriv F)) (Ioo (1 : ℝ) 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 1 2)
  · intro u hu
    exact ((approximateModelPhase_deriv_contDiffAt hF hu).derivWithin
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).continuousAt.continuousWithinAt
  · intro u hu
    have hui : u ∈ Ioo (1 : ℝ) 2 := by simpa using hu
    exact (modelPhaseThirdLower_pos hσ).trans_le
      (approximateModelPhase_thirdDeriv_bounds hσ hδ hF hui).1

theorem modelPhaseInverseSlope_antitoneOn
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    AntitoneOn (modelPhaseInverseSlope F) (modelPhaseSlopeRange F) := by
  intro v hv w hw hvw
  by_contra hn
  have hlt : modelPhaseInverseSlope F v < modelPhaseInverseSlope F w :=
    lt_of_not_ge hn
  have h := approximateModelPhase_deriv_strictAntiOn hσ hδ hF
    (modelPhaseInverseSlope_mem hv) (modelPhaseInverseSlope_mem hw) hlt
  rw [deriv_modelPhaseInverseSlope_apply hv,deriv_modelPhaseInverseSlope_apply hw] at h
  exact (not_lt_of_ge hvw) h

theorem modelPhaseStationaryAmplitude_antitoneOn
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ) :
    AntitoneOn (modelPhaseStationaryAmplitude F) (modelPhaseSlopeRange F) := by
  have hd₁ : δ ≤ min (modelPhaseCurvatureLower σ) 1 := hδ.trans (min_le_left _ _)
  have hd₂ : δ ≤ min (modelPhaseThirdLower σ) 1 := hδ.trans (min_le_right _ _)
  have hF₁ := approximateModelPhase_mono hF (by norm_num : 1 ≤ 2) le_rfl
  intro v hv w hw hvw
  have hi := modelPhaseInverseSlope_antitoneOn hσ hd₁ hF₁ hv hw hvw
  have hq : modelPhaseCurvatureAt F v ≤ modelPhaseCurvatureAt F w := by
    exact neg_le_neg ((approximateModelPhase_secondDeriv_strictMonoOn hσ hd₂ hF).monotoneOn
      (modelPhaseInverseSlope_mem hw) (modelPhaseInverseSlope_mem hv) hi)
  exact inv_anti₀ (Real.sqrt_pos.mpr (modelPhaseCurvatureAt_pos hσ hd₁ hF₁ hv))
    (Real.sqrt_le_sqrt hq)

end TaoTrudgianYang2025

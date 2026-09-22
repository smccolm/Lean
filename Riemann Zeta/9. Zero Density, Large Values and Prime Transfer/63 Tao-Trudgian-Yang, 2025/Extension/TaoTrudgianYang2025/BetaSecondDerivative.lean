import TaoTrudgianYang2025.BetaUniformity
import GuthMaynard.SecondOrderMeanValue

/-!
# Model-phase curvature for the beta endpoint

The second-derivative input is derived from the actual approximate-model
condition on [1,2]. No exponential-sum estimate is assumed.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025

def modelPhaseCurvatureLower (σ : ℝ) : ℝ := σ*2^(-σ-1)/2

theorem modelPhaseCurvatureLower_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseCurvatureLower σ := by
  unfold modelPhaseCurvatureLower
  positivity

theorem approximateModelPhase_curvature_bounds {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    modelPhaseCurvatureLower σ ≤ -iteratedDerivWithin 2 F phaseInterval u ∧
      -iteratedDerivWithin 2 F phaseInterval u ≤ σ+1 := by
  have he := hF.2 1 le_rfl ⟨u,hu⟩
  rw [modelPhaseErrorAt, iteratedDerivWithin_modelPhase σ 1 hu] at he
  norm_num at he
  rw [abs_le] at he
  have huPos : 0 < u := zero_lt_one.trans_le hu.1
  have hlow : (2 : ℝ)^(-σ-1) ≤ u^(-σ-1) :=
    Real.rpow_le_rpow_of_nonpos huPos hu.2 (by linarith)
  have hhigh : u^(-σ-1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu.1 (by linarith)
  have hd₀ := hδ.trans (min_le_left _ _)
  have hd₁ := hδ.trans (min_le_right _ _)
  unfold modelPhaseCurvatureLower at hd₀ ⊢
  constructor <;> nlinarith

theorem approximateModelPhase_curvature_deriv_bounds {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ ≤ -deriv (deriv F) u ∧
      -deriv (deriv F) u ≤ σ+1 := by
  have huClosed : u ∈ phaseInterval := ⟨hu.1.le,hu.2.le⟩
  have hcont : ContDiffAt ℝ 2 F u :=
    (hF.1.contDiffAt (Icc_mem_nhds hu.1 hu.2)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h := approximateModelPhase_curvature_bounds hσ hδ hF huClosed
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hcont huClosed] at h
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h

end TaoTrudgianYang2025

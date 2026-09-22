import TaoTrudgianYang2025.BetaStationaryDeficit
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The quadratic coordinate is differentiable at the stationary point

The Taylor remainder is taken from the actual original phase on (1,2).
It determines the signed square-root coordinate's slope at the critical
point, including the removable zero in the divided deficit.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem modelPhaseMorseCoordinate_at_inverse (F : ℝ → ℝ) (v : ℝ) :
    modelPhaseMorseCoordinate F v (modelPhaseInverseSlope F v) = 0 := by
  simp only [modelPhaseMorseCoordinate,lt_self_iff_false,if_false,
    modelPhaseStationaryDeficit_at_inverse,mul_zero,Real.sqrt_zero]

theorem modelPhaseStationaryDeficit_ratio_tendsto
    {F : ℝ → ℝ} {σ δ v : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    Tendsto (fun u : ℝ => 2*modelPhaseStationaryDeficit F v u /
      (u-modelPhaseInverseSlope F v)^2)
      (𝓝[≠] modelPhaseInverseSlope F v) (𝓝 (modelPhaseCurvatureAt F v)) := by
  let u₀ := modelPhaseInverseSlope F v
  have hu₀ : u₀ ∈ Ioo (1 : ℝ) 2 := modelPhaseInverseSlope_mem hv
  have hs : ContDiffOn ℝ 2 F (Ioo (1 : ℝ) 2) := by
    intro x hx
    exact ((approximateModelPhase_contDiffAt hF hx).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffWithinAt
  have hfirst : iteratedDerivWithin 1 F (Ioo (1 : ℝ) 2) u₀ = v := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo 1 2)
      ((approximateModelPhase_contDiffAt hF hu₀).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hu₀,iteratedDeriv_one]
    exact deriv_modelPhaseInverseSlope_apply hv
  have hsecond : iteratedDerivWithin 2 F (Ioo (1 : ℝ) 2) u₀ =
      deriv (deriv F) u₀ := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo 1 2)
      ((approximateModelPhase_contDiffAt hF hu₀).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hu₀]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  have hpoly (u : ℝ) : taylorWithinEval F 2 (Ioo (1 : ℝ) 2) u₀ u =
      F u₀+(u-u₀)*v+(u-u₀)^2/2*deriv (deriv F) u₀ := by
    rw [taylorWithinEval_succ F 1,taylorWithinEval_succ F 0,taylor_within_zero_eval]
    rw [hfirst,hsecond]
    norm_num only [Nat.factorial_zero,Nat.factorial_one,smul_eq_mul]
    ring
  have ht := Real.taylor_tendsto (n := 2) (convex_Ioo 1 2) hu₀ hs
  rw [nhdsWithin_eq_nhds.mpr (isOpen_Ioo.mem_nhds hu₀)] at ht
  have ht' := ht.mono_left (show 𝓝[≠] u₀ ≤ 𝓝 u₀ from inf_le_left)
  have hlim : Tendsto (fun u : ℝ => modelPhaseCurvatureAt F v -
      2*((F u-taylorWithinEval F 2 (Ioo (1 : ℝ) 2) u₀ u)/(u-u₀)^2))
      (𝓝[≠] u₀) (𝓝 (modelPhaseCurvatureAt F v)) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul ht'))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hne : u-u₀ ≠ 0 := sub_ne_zero.mpr hu
  rw [hpoly]
  unfold modelPhaseStationaryDeficit modelPhaseCurvatureAt
  change -deriv (deriv F) u₀ -
    2*((F u-(F u₀+(u-u₀)*v+(u-u₀)^2/2*deriv (deriv F) u₀))/(u-u₀)^2) =
      2*(F u₀+v*(u-u₀)-F u)/(u-u₀)^2
  field_simp
  ring

theorem modelPhaseMorseCoordinate_slope (F : ℝ → ℝ) (v u : ℝ) :
    slope (modelPhaseMorseCoordinate F v) (modelPhaseInverseSlope F v) u =
      Real.sqrt (2*modelPhaseStationaryDeficit F v u /
        (u-modelPhaseInverseSlope F v)^2) := by
  rw [slope,modelPhaseMorseCoordinate_at_inverse,vsub_eq_sub,sub_zero,smul_eq_mul,
    Real.sqrt_div' _ (sq_nonneg _),Real.sqrt_sq_eq_abs]
  unfold modelPhaseMorseCoordinate
  split_ifs with h
  · rw [abs_of_neg (sub_neg.mpr h)]
    field_simp
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt h))]
    ring

theorem modelPhaseMorseCoordinate_hasDerivAt_inverse
    {F : ℝ → ℝ} {σ δ v : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseMorseCoordinate F v) (Real.sqrt (modelPhaseCurvatureAt F v))
      (modelPhaseInverseSlope F v) := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (modelPhaseStationaryDeficit_ratio_tendsto hF hv)
  exact h.congr' (Eventually.of_forall (fun u => (modelPhaseMorseCoordinate_slope F v u).symm))

theorem modelPhaseMorseCoordinate_reciprocal_derivative_amplitude
    {F : ℝ → ℝ} {σ δ v : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    (deriv (modelPhaseMorseCoordinate F v) (modelPhaseInverseSlope F v))⁻¹ =
      modelPhaseStationaryAmplitude F v := by
  rw [(modelPhaseMorseCoordinate_hasDerivAt_inverse hF hv).deriv]
  rfl

end TaoTrudgianYang2025

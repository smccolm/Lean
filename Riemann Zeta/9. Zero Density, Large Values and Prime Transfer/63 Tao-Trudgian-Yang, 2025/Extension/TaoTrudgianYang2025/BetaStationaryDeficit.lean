import TaoTrudgianYang2025.BetaStationaryBetaBound
import Mathlib.Analysis.Calculus.Taylor

/-!
# Actual stationary deficit and exact quadratic coordinates

Curvature bounds give a two-sided quadratic bound for the original
phase deficit about its inverse-slope point. The signed square-root
coordinate gives an exact quadratic phase, with quantitative distance
bounds. Smooth invertibility and transformed-integral error estimates
are separate obligations.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def modelPhaseStationaryDeficit (F : ℝ → ℝ) (v u : ℝ) : ℝ :=
  F (modelPhaseInverseSlope F v) + v*(u-modelPhaseInverseSlope F v)-F u

def modelPhaseMorseCoordinate (F : ℝ → ℝ) (v u : ℝ) : ℝ :=
  if u < modelPhaseInverseSlope F v then
    -Real.sqrt (2*modelPhaseStationaryDeficit F v u)
  else Real.sqrt (2*modelPhaseStationaryDeficit F v u)

theorem modelPhaseStationaryDeficit_at_inverse (F : ℝ → ℝ) (v : ℝ) :
    modelPhaseStationaryDeficit F v (modelPhaseInverseSlope F v) = 0 := by
  simp only [modelPhaseStationaryDeficit,sub_self,mul_zero,add_zero]

theorem modelPhaseStationaryDeficit_bounds
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ*(u-modelPhaseInverseSlope F v)^2/2 ≤
        modelPhaseStationaryDeficit F v u ∧
      modelPhaseStationaryDeficit F v u ≤
        (σ+1)*(u-modelPhaseInverseSlope F v)^2/2 := by
  let u₀ := modelPhaseInverseSlope F v
  have hu₀ : u₀ ∈ Ioo (1 : ℝ) 2 := modelPhaseInverseSlope_mem hv
  by_cases heq : u₀ = u
  · rw [← heq]
    simp only [u₀,modelPhaseStationaryDeficit_at_inverse,sub_self,zero_pow (by decide : 2 ≠ 0),
      mul_zero,zero_div,le_refl,and_self]
  · have hsub : uIcc u₀ u ⊆ Ioo (1 : ℝ) 2 :=
      ordConnected_Ioo.uIcc_subset hu₀ hu
    have hs : ContDiffOn ℝ 2 F (uIcc u₀ u) := by
      intro x hx
      exact ((approximateModelPhase_contDiffAt hF (hsub hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffWithinAt
    have huniq : UniqueDiffOn ℝ (uIcc u₀ u) := uniqueDiffOn_Icc (by
      rcases lt_or_gt_of_ne heq with h | h
      · simpa only [min_eq_left h.le,max_eq_right h.le] using h
      · simpa only [min_eq_right h.le,max_eq_left h.le] using h)
    have hfirst : iteratedDerivWithin 1 F (uIcc u₀ u) u₀ = v := by
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq
        ((approximateModelPhase_contDiffAt hF hu₀).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) left_mem_uIcc,iteratedDeriv_one]
      exact deriv_modelPhaseInverseSlope_apply hv
    have hpoly : taylorWithinEval F 1 (uIcc u₀ u) u₀ u =
        F u₀+(u-u₀)*v := by
      rw [show (1 : ℕ) = 0+1 by rfl,taylorWithinEval_succ,taylor_within_zero_eval]
      norm_num [hfirst]
    obtain ⟨x,hx,hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) heq hs
    rw [hpoly] at hrem
    norm_num only [Nat.reduceAdd,Nat.factorial_two,Nat.cast_ofNat,iteratedDeriv_succ,
      iteratedDeriv_zero] at hrem
    have hxI : x ∈ Ioo (1 : ℝ) 2 := hsub (Ioo_subset_Icc_self hx)
    have hc := approximateModelPhase_curvature_deriv_bounds hσ hδ hF hxI
    have hd : modelPhaseStationaryDeficit F v u =
        (-deriv (deriv F) x)*(u-u₀)^2/2 := by
      unfold modelPhaseStationaryDeficit
      change F u₀+v*(u-u₀)-F u = _
      nlinarith only [hrem]
    rw [hd]
    exact ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc.1 (sq_nonneg _))
      (by norm_num),div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc.2 (sq_nonneg _))
      (by norm_num)⟩

theorem modelPhaseStationaryDeficit_nonneg
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    0 ≤ modelPhaseStationaryDeficit F v u := by
  have h : 0 ≤ modelPhaseCurvatureLower σ*(u-modelPhaseInverseSlope F v)^2/2 := by
    positivity [modelPhaseCurvatureLower_pos hσ]
  exact h.trans (modelPhaseStationaryDeficit_bounds hσ hδ hF hv hu).1

theorem modelPhaseMorseCoordinate_sq
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    (modelPhaseMorseCoordinate F v u)^2 = 2*modelPhaseStationaryDeficit F v u := by
  have hp := modelPhaseStationaryDeficit_nonneg hσ hδ hF hv hu
  unfold modelPhaseMorseCoordinate
  split_ifs <;> simp only [neg_sq,Real.sq_sqrt (by positivity : 0 ≤ 2*modelPhaseStationaryDeficit F v u)]

theorem modelPhaseMorseCoordinate_abs
    (F : ℝ → ℝ) (v u : ℝ) :
    |modelPhaseMorseCoordinate F v u| = Real.sqrt (2*modelPhaseStationaryDeficit F v u) := by
  unfold modelPhaseMorseCoordinate
  split_ifs <;> simp only [abs_neg,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem modelPhaseMorseCoordinate_bounds
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    Real.sqrt (modelPhaseCurvatureLower σ)*|u-modelPhaseInverseSlope F v| ≤
        |modelPhaseMorseCoordinate F v u| ∧
      |modelPhaseMorseCoordinate F v u| ≤
        Real.sqrt (σ+1)*|u-modelPhaseInverseSlope F v| := by
  have hb := modelPhaseStationaryDeficit_bounds hσ hδ hF hv hu
  have hl : modelPhaseCurvatureLower σ*(u-modelPhaseInverseSlope F v)^2 ≤
      2*modelPhaseStationaryDeficit F v u := by linarith [hb.1]
  have hr : 2*modelPhaseStationaryDeficit F v u ≤
      (σ+1)*(u-modelPhaseInverseSlope F v)^2 := by linarith [hb.2]
  have hsl := Real.sqrt_le_sqrt hl
  have hsr := Real.sqrt_le_sqrt hr
  rw [Real.sqrt_mul (modelPhaseCurvatureLower_pos hσ).le,Real.sqrt_sq_eq_abs] at hsl
  rw [Real.sqrt_mul (by linarith : 0 ≤ σ+1),Real.sqrt_sq_eq_abs] at hsr
  rw [modelPhaseMorseCoordinate_abs]
  exact ⟨hsl,hsr⟩

theorem modelPhaseMorseCoordinate_normalForm
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    F u-v*u = -modelPhaseLegendreDual F v-(modelPhaseMorseCoordinate F v u)^2/2 := by
  rw [modelPhaseMorseCoordinate_sq hσ hδ hF hv hu]
  unfold modelPhaseLegendreDual modelPhaseStationaryDeficit
  ring

theorem modelPhaseFrequencyPhase_deficit
    {F : ℝ → ℝ} {T N : ℝ} (hT : T ≠ 0) (hN : N ≠ 0) (r x : ℝ) :
    modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) -
        modelPhaseFrequencyPhase F T N r x =
      T*modelPhaseStationaryDeficit F (r*N/T) (x/N) := by
  unfold modelPhaseFrequencyPhase
  rw [modelPhaseStationaryPoint_div hN]
  unfold modelPhaseStationaryPoint modelPhaseStationaryDeficit
  field_simp
  ring

theorem modelPhaseFrequencyPhase_quadratic_normalForm
    {σ δ T N r x : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) (hx : x/N ∈ Ioo (1 : ℝ) 2) :
    modelPhaseFrequencyPhase F T N r x =
      modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) -
        (T/2)*(modelPhaseMorseCoordinate F (r*N/T) (x/N))^2 := by
  have h := modelPhaseFrequencyPhase_deficit (F := F) hT hN r x
  rw [modelPhaseMorseCoordinate_sq hσ hδ hF hv hx]
  linarith

end TaoTrudgianYang2025

import TaoTrudgianYang2025.BetaReferencePhase
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform original-phase derivative errors at the inverse point

Every reference derivative has an explicit Pochhammer bound on [1,2].
Mean value and the proved inverse displacement transfer the original model
errors to the actual inverse point, at each requested derivative order.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def modelPhaseJetCoefficient (σ : ℝ) (p : ℕ) : ℝ :=
  |(descPochhammer ℝ p).eval (-σ)|

theorem modelPhaseJetCoefficient_nonneg (σ : ℝ) (p : ℕ) :
    0 ≤ modelPhaseJetCoefficient σ p :=
  abs_nonneg _

theorem approximateModelPhase_iteratedDeriv_error
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F u - iteratedDeriv p (modelPhase σ) u| ≤ δ := by
  have he := hF.2 p hp ⟨u, hu.1.le, hu.2.le⟩
  have hc : ContDiffAt ℝ (p+1) F u :=
    (approximateModelPhase_contDiffAt hF hu).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1))
  have hm : ContDiffAt ℝ p (modelPhase σ) u :=
    Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hu.1).ne'
  change ‖iteratedDerivWithin (p+1) F phaseInterval u -
    iteratedDerivWithin p (modelPhase σ) phaseInterval u‖ ≤ δ at he
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hc
    ⟨hu.1.le,hu.2.le⟩, iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hm
    ⟨hu.1.le,hu.2.le⟩, Real.norm_eq_abs] at he
  exact he

theorem iteratedDeriv_modelPhase_abs_le {σ : ℝ} (hσ : 0 ≤ σ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) :
    |iteratedDeriv p (modelPhase σ) u| ≤ modelPhaseJetCoefficient σ p := by
  have hm : ContDiffAt ℝ p (modelPhase σ) u :=
    Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hu.1).ne'
  have hb := norm_iteratedDerivWithin_modelPhase_le hσ p ⟨hu.1.le,hu.2.le⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hm
    ⟨hu.1.le,hu.2.le⟩] at hb
  exact hb

theorem iteratedDeriv_modelPhase_lipschitz {σ : ℝ} (hσ : 0 ≤ σ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2) (p : ℕ) :
    |iteratedDeriv p (modelPhase σ) u - iteratedDeriv p (modelPhase σ) w| ≤
      modelPhaseJetCoefficient σ (p+1) * |u-w| := by
  have hd : ∀ x ∈ Ioo (1 : ℝ) 2, DifferentiableAt ℝ (iteratedDeriv p (modelPhase σ)) x := by
    intro x hx
    exact (contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hx.1).ne') p).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hb : ∀ x ∈ Ioo (1 : ℝ) 2,
      ‖deriv (iteratedDeriv p (modelPhase σ)) x‖ ≤ modelPhaseJetCoefficient σ (p+1) := by
    intro x hx
    rw [← iteratedDeriv_succ]
    exact iteratedDeriv_modelPhase_abs_le hσ hx (p+1)
  exact Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Ioo 1 2) hw hu

theorem approximateModelPhase_iteratedDeriv_reference_gap
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2)
    (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F u -
      iteratedDeriv (p+1) (referenceModelPrimitive σ) w| ≤
      δ + modelPhaseJetCoefficient σ (p+1) * |u-w| := by
  rw [referenceModelPrimitive_iteratedDeriv σ (zero_lt_one.trans hw.1) p]
  exact (abs_sub_le _ _ _).trans (add_le_add
    (approximateModelPhase_iteratedDeriv_error hF hu p hp)
    (iteratedDeriv_modelPhase_lipschitz hσ hu hw p))

theorem modelPhaseInverse_iteratedDeriv_reference_error
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F (modelPhaseInverseSlope F v) -
      iteratedDeriv (p+1) (referenceModelPrimitive σ)
        (modelPhaseInverseSlope (referenceModelPrimitive σ) v)| ≤
      (1 + modelPhaseJetCoefficient σ (p+1) / modelPhaseCurvatureLower σ) * δ := by
  rw [referenceModelPrimitive_inverse hσ hm]
  have hg := approximateModelPhase_iteratedDeriv_reference_gap hσ.le hF
    (modelPhaseInverseSlope_mem hv) (reciprocal_modelPhase_mem hσ hm) p hp
  have hi := modelPhaseInverseSlope_model_error hσ hδ
    (approximateModelPhase_mono hF hP le_rfl) hv hm
  have hb := mul_le_mul_of_nonneg_left hi (modelPhaseJetCoefficient_nonneg σ (p+1))
  calc
    _ ≤ δ+modelPhaseJetCoefficient σ (p+1) * |modelPhaseInverseSlope F v-v^(-σ⁻¹)| := hg
    _ ≤ δ+modelPhaseJetCoefficient σ (p+1)*(δ/modelPhaseCurvatureLower σ) :=
      add_le_add le_rfl hb
    _ = _ := by ring

theorem inverse_difference_le_curvature {a b c : ℝ}
    (hc : 0 < c) (ha : c ≤ -a) (hb : c ≤ -b) :
    |a⁻¹-b⁻¹| ≤ |a-b|/c^2 := by
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have ha' : a < 0 := by linarith
  have hb' : b < 0 := by linarith
  have he : a⁻¹-b⁻¹ = (b-a)/(a*b) := by field_simp
  rw [he, abs_div, abs_mul, abs_sub_comm, abs_of_neg ha', abs_of_neg hb']
  apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hc)
  nlinarith

end TaoTrudgianYang2025

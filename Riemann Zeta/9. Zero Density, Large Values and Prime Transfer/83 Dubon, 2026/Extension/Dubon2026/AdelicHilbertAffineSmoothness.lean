import Dubon2026.AdelicAffineHolomorphicFormula

/-! # Joint affine smoothness of the original completed adelic generator -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory Filter
open scoped MatrixGroups ContDiff Topology

/-- The actual two real affine coordinates give a smooth complex upper-half-plane parameter. -/
theorem realAffineHolomorphicParameter_contDiff :
    ContDiff ℝ ∞ (fun v : ℝ × ℝ => realAffineHolomorphicParameter v.1 v.2) := by
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
    ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_snd)).mul
      contDiff_const) |>.sub contDiff_const

/-- The genuine holomorphic L2 slice is smooth as a real map at every point of its proved disk. -/
theorem adelicHolomorphicL2Curve_contDiffAt (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {z : ℂ}
    (hz : ‖z‖ < (1 / 2 : ℝ)) : ContDiffAt ℝ ∞ (adelicHolomorphicL2Curve N f) z := by
  have hm : z ∈ Metric.ball 0 (1 / 2 : ℝ) := by simpa using hz
  exact (((adelicHolomorphicL2Curve_differentiableOn N f).contDiffOn Metric.isOpen_ball).contDiffAt
    (Metric.isOpen_ball.mem_nhds hm)).restrict_scalars ℝ

/-- The original affine generator orbit is jointly smooth in its two real coordinates near the identity. -/
theorem adelicCyclicHilbertGenerator_affine_contDiffAt {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {v : ℝ × ℝ}
    (hv : ‖realAffineHolomorphicParameter v.1 v.2‖ < (1 / 2 : ℝ)) :
    ContDiffAt ℝ ∞ (fun w : ℝ × ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realAffineMatrix w.1 (Real.exp_pos w.2)))
      (adelicCyclicHilbertGenerator f)) v := by
  have hH := (adelicHolomorphicL2Curve_contDiffAt N f hv).comp v
    realAffineHolomorphicParameter_contDiff.contDiffAt
  have hr := @ContinuousLinearMap.contDiff ℝ
    (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance inferInstance ∞
    ((adelicCyclicHilbertL2Retraction f).restrictScalars ℝ)
  have hR := hr.contDiffAt.comp v hH
  have he : ContDiff ℝ ∞ (fun w : ℝ × ℝ => (Real.exp (w.2 * ((k : ℝ) / 2)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_snd.mul contDiff_const))
  have ht := he.contDiffAt.smul hR
  apply ht.congr_of_eventuallyEq
  have hnb : ∀ᶠ w : ℝ × ℝ in 𝓝 v,
      ‖realAffineHolomorphicParameter w.1 w.2‖ < (1 / 2 : ℝ) :=
    (realAffineHolomorphicParameter_contDiff.continuous.norm.isOpen_preimage
      (Set.Iio (1 / 2 : ℝ)) isOpen_Iio).mem_nhds hv
  filter_upwards [hnb] with w hw
  exact adelicCyclicHilbertGenerator_affine_formula f w.1 w.2 hw

/-- Joint affine smoothness holds at the actual identity coordinate without any additional premise. -/
theorem adelicCyclicHilbertGenerator_affine_contDiffAt_zero {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ContDiffAt ℝ ∞ (fun w : ℝ × ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realAffineMatrix w.1 (Real.exp_pos w.2)))
      (adelicCyclicHilbertGenerator f)) 0 := by
  apply adelicCyclicHilbertGenerator_affine_contDiffAt f
  norm_num [realAffineHolomorphicParameter]

end
end Dubon2026

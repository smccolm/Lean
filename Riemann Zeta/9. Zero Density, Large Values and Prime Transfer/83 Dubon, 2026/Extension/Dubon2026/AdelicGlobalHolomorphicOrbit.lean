import Dubon2026.AdelicNormalizedHolomorphicOrbit

/-! # Holomorphy of the original normalized Hilbert orbit on the full upper half-plane -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Filter
open scoped MatrixGroups Topology

private theorem continuousLinearMap_differentiableOn_comp {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : V →L[ℂ] W) (H : ℂ → V) (s : Set ℂ) (hH : DifferentiableOn ℂ H s) :
    DifferentiableOn ℂ (fun z => T (H z)) s :=
  fun z hz => T.differentiableAt.comp_differentiableWithinAt z (hH z hz)

private theorem differentiableAt_of_local_affine_formula {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (F H : ℂ → V) (z₀ a b : ℂ) (T : V →L[ℂ] V)
    (hH : DifferentiableOn ℂ H (Metric.ball 0 (1 / 2 : ℝ)))
    (he : F =ᶠ[𝓝 z₀] (fun z => a • T (H ((z - z₀) / b)))) : DifferentiableAt ℂ F z₀ := by
  have hH₀ : DifferentiableAt ℂ H ((z₀ - z₀) / b) :=
    hH.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))
  have hd : DifferentiableAt ℂ (fun z : ℂ => (z - z₀) / b) z₀ := by fun_prop
  exact ((T.differentiableAt.comp z₀ (hH₀.comp z₀ hd)).const_smul a).congr_of_eventuallyEq he

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual retracted L2 slice is holomorphic in the original Hilbert norm on its genuine disk. -/
theorem adelicHolomorphicHilbertCurve_differentiableOn :
    DifferentiableOn ℂ (adelicHolomorphicHilbertCurve f) (Metric.ball 0 (1 / 2 : ℝ)) := by
  exact @continuousLinearMap_differentiableOn_comp
    (MeasureTheory.Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertL2Retraction f) (adelicHolomorphicL2Curve N f) _
    (adelicHolomorphicL2Curve_differentiableOn N f)

/-- The original normalized affine orbit is genuinely holomorphic at every original upper-half-plane point. -/
theorem adelicNormalizedAffineHilbertOrbit_differentiableAt {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    DifferentiableAt ℂ (adelicNormalizedAffineHilbertOrbit f) z₀ := by
  apply @differentiableAt_of_local_affine_formula (AdelicCyclicHilbert f)
    inferInstance inferInstance (adelicNormalizedAffineHilbertOrbit f)
    (adelicHolomorphicHilbertCurve f) z₀
    ((Real.exp (Real.log z₀.im * ((k : ℝ) / 2)) : ℂ))⁻¹ (z₀.im : ℂ)
    (adelicCyclicHilbertOperator f (adelicRealSL2Embedding (realAffineMatrix z₀.re hz₀)))
    (adelicHolomorphicHilbertCurve_differentiableOn f)
  have hc : Continuous (fun z : ℂ => ‖(z - z₀) / (z₀.im : ℂ)‖) := by fun_prop
  have hn : ∀ᶠ z : ℂ in 𝓝 z₀, ‖(z - z₀) / (z₀.im : ℂ)‖ < (1 / 2 : ℝ) :=
    (hc.isOpen_preimage (Set.Iio (1 / 2 : ℝ)) isOpen_Iio).mem_nhds (by simp)
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz₀, hn] with z hz hn
  exact adelicNormalizedAffineHilbertOrbit_local_formula f hz hz₀ hn

/-- The actual normalized affine Hilbert orbit is holomorphic on the entire original upper half-plane. -/
theorem adelicNormalizedAffineHilbertOrbit_differentiableOn :
    DifferentiableOn ℂ (adelicNormalizedAffineHilbertOrbit f) upperHalfPlaneSet :=
  fun _ hz => (adelicNormalizedAffineHilbertOrbit_differentiableAt f hz).differentiableWithinAt

end
end Dubon2026

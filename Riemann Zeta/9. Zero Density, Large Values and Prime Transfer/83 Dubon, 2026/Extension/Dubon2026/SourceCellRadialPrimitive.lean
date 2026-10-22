import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Star
import Mathlib.Tactic

/-! DUB-17/18 -> raw reciprocity -> cellwise regular-differential primitives.
Radial integration constructs a normalized primitive on an open star-convex
complex domain. A single compact product bound for the parameter derivative
replaces the separate function/derivative bounds and norm estimates in the source.
Adapted from S_Complex_exists_hasDerivAt_of_starConvex, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open scoped Interval Topology
open Set Filter MeasureTheory intervalIntegral Metric

theorem exists_radial_primitive {U : Set ℂ} (hU : IsOpen U) {q : ℂ}
    (hstar : StarConvex ℝ q U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ g : ℂ → ℂ, g q = 0 ∧ ∀ z ∈ U, HasDerivAt g (f z) z := by

  have hseg : ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, q + (t : ℂ) * (z - q) ∈ U := by
    intro z hz t ht
    have h := hstar hz (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
    have heq : (1 - t) • q + t • z = q + (t : ℂ) * (z - q) := by
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [heq] at h
    exact h

  set F : ℂ → ℝ → ℂ := fun w t => (w - q) * f (q + (t : ℂ) * (w - q)) with hF
  set F' : ℂ → ℝ → ℂ := fun w t =>
    f (q + (t : ℂ) * (w - q)) + (w - q) * ((t : ℂ) * deriv f (q + (t : ℂ) * (w - q))) with hF'

  have hfc : ContinuousOn f U := hf.continuousOn
  have hf'c : ContinuousOn (deriv f) U := ((hf.analyticOnNhd hU).deriv).continuousOn

  have hpath : ∀ w, Continuous fun t : ℝ => q + (t : ℂ) * (w - q) := by
    intro w; fun_prop
  have hFc : ∀ w ∈ U, ContinuousOn (F w) (Icc (0 : ℝ) 1) := by
    intro w hw
    refine continuousOn_const.mul (hfc.comp (hpath w).continuousOn fun t ht => hseg w hw t ht)
  have hF'c : ∀ w ∈ U, ContinuousOn (F' w) (Icc (0 : ℝ) 1) := by
    intro w hw
    refine (hfc.comp (hpath w).continuousOn fun t ht => hseg w hw t ht).add ?_
    refine continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul ?_)
    exact hf'c.comp (hpath w).continuousOn fun t ht => hseg w hw t ht
  have hmeas : ∀ G : ℝ → ℂ, ContinuousOn G (Icc (0 : ℝ) 1) →
      AEStronglyMeasurable G (volume.restrict (Ι (0 : ℝ) 1)) := by
    intro G hG
    rw [uIoc_of_le zero_le_one]
    exact (hG.aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  refine ⟨fun w => ∫ t in (0 : ℝ)..1, F w t, ?_, fun z₀ hz₀ => ?_⟩
  · simp only [hF, sub_self, zero_mul, intervalIntegral.integral_zero]

  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, closedBall z₀ δ ⊆ U :=
    nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz₀)
  have hp2 : Continuous (fun p : ℂ × ℝ => q + (p.2 : ℂ) * (p.1 - q)) := by fun_prop
  have hmaps : MapsTo (fun p : ℂ × ℝ => q + (p.2 : ℂ) * (p.1 - q))
      (closedBall z₀ δ ×ˢ Icc (0 : ℝ) 1) U := fun p hp => hseg p.1 (hball hp.1) p.2 hp.2
  have hF'joint : ContinuousOn (fun p : ℂ × ℝ => F' p.1 p.2)
      (closedBall z₀ δ ×ˢ Icc (0 : ℝ) 1) :=
    (hfc.comp hp2.continuousOn hmaps).add
      ((continuous_fst.continuousOn.sub continuousOn_const).mul
        ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul
          (hf'c.comp hp2.continuousOn hmaps)))
  obtain ⟨M, hM⟩ := ((isCompact_closedBall z₀ δ).prod isCompact_Icc).exists_bound_of_continuousOn hF'joint
  have hpoint : ∀ w ∈ closedBall z₀ δ, ∀ t ∈ Ι (0 : ℝ) 1, q + (t : ℂ) * (w - q) ∈ U := by
    intro w hw t ht
    rw [uIoc_of_le zero_le_one] at ht
    exact hseg w (hball hw) t (Ioc_subset_Icc_self ht)
  have hdiffF : ∀ t ∈ Ι (0 : ℝ) 1, ∀ w ∈ closedBall z₀ δ,
      HasDerivAt (fun w => F w t) (F' w t) w := by
    intro t ht w hw
    have hp : q + (t : ℂ) * (w - q) ∈ U := hpoint w hw t ht
    have h1 : HasDerivAt (fun w : ℂ => w - q) 1 w := (hasDerivAt_id w).sub_const q
    have h2 : HasDerivAt (fun w : ℂ => q + (t : ℂ) * (w - q)) ((t : ℂ) * 1) w :=
      (h1.const_mul (t : ℂ)).const_add q
    have h3 : HasDerivAt f (deriv f (q + (t : ℂ) * (w - q))) (q + (t : ℂ) * (w - q)) :=
      (hf.differentiableAt (hU.mem_nhds hp)).hasDerivAt
    have h4 := h1.mul (h3.comp w h2)
    refine h4.congr_deriv ?_
    simp only [hF', mul_one, one_mul, Function.comp_apply]
    ring
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1, ∀ w ∈ closedBall z₀ δ, ‖F' w t‖ ≤ M := by
    intro t ht w hw
    rw [uIoc_of_le zero_le_one] at ht
    exact hM (w, t) ⟨hw, Ioc_subset_Icc_self ht⟩
  have hz₀U : ∀ᶠ w in 𝓝 z₀, w ∈ U := hU.mem_nhds hz₀
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (F := F) (F' := F') (x₀ := z₀) (s := closedBall z₀ δ)
    (bound := fun _ => M)
    (closedBall_mem_nhds z₀ hδ)
    (hz₀U.mono fun w hw => hmeas _ (hFc w hw))
    ((hFc z₀ hz₀).intervalIntegrable_of_Icc (zero_le_one' ℝ))
    (hmeas _ (hF'c z₀ hz₀))
    (Eventually.of_forall fun t ht w hw => hbound t ht w hw)
    _root_.intervalIntegrable_const
    (Eventually.of_forall fun t ht w hw => hdiffF t ht w hw)

  have hval : (∫ t in (0 : ℝ)..1, F' z₀ t) = f z₀ := by
    set v : ℂ := z₀ - q with hv
    have hG : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) * f (q + (t : ℂ) * v)) (F' z₀ t) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hp : q + (t : ℂ) * v ∈ U := hseg z₀ hz₀ t ht
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun t : ℝ => q + (t : ℂ) * v) (1 * v) t :=
        (h1.mul_const v).const_add q
      have h3 : HasDerivAt f (deriv f (q + (t : ℂ) * v)) (q + (t : ℂ) * v) :=
        (hf.differentiableAt (hU.mem_nhds hp)).hasDerivAt
      have h4 := h1.mul (h3.comp t h2)
      refine h4.congr_deriv ?_
      simp only [hF', one_mul, Function.comp_apply, hv]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
      ((hF'c z₀ hz₀).intervalIntegrable_of_Icc (zero_le_one' ℝ))]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, sub_zero]
    congr 1
    rw [hv]
    ring
  rw [← hval]
  exact key.2

end
end Dubon2026.SourceFunctionField.CellGeometry

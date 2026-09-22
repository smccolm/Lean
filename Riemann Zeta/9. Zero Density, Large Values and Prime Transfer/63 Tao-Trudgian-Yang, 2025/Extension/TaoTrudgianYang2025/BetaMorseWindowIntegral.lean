import TaoTrudgianYang2025.BetaBufferedMorseLocal

/-!
# Exact transport of the central integral

The original cutoff and phase are retained on the inverse image of a
closed quadratic window. The change of variables uses the actual smooth
inverse and its actual positive Jacobian.
-/

noncomputable section

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology FourierTransform

namespace TaoTrudgianYang2025

theorem integral_inverseMorse_window
    {F : ℝ → ℝ} {σ δ v H : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hH : 0 ≤ H)
    (hs : Icc (-H) H ⊆ modelPhaseMorseRange F v)
    {g : ℝ → ℂ} (hg : ContinuousOn g (Ioo (1 : ℝ) 2)) :
    (∫ u in modelPhaseMorseInverse F v (-H)..modelPhaseMorseInverse F v H, g u) =
      ∫ z in (-H)..H, ((deriv (modelPhaseMorseInverse F v) z : ℝ) : ℂ)*
        g (modelPhaseMorseInverse F v z) := by
  have hs' : uIcc (-H) H ⊆ modelPhaseMorseRange F v := by
    rwa [uIcc_of_le (by linarith : -H ≤ H)]
  have hd : ∀ z ∈ uIcc (-H) H, HasDerivAt (modelPhaseMorseInverse F v)
      (deriv (modelPhaseMorseInverse F v) z) z := fun z hz => (modelPhaseMorseInverse_hasStrictDerivAt hσ hδ hF hv (hs' hz)).hasDerivAt.differentiableAt.hasDerivAt
  have hc : ContinuousOn (deriv (modelPhaseMorseInverse F v)) (uIcc (-H) H) := by
    intro z hz
    exact ((modelPhaseMorseInverse_contDiffAt hσ hδ hF hv (hs' hz)).derivWithin (m := ∞)
      (by simp)).continuousAt.continuousWithinAt
  have hi : modelPhaseMorseInverse F v '' uIcc (-H) H ⊆ Ioo (1 : ℝ) 2 := by
    rintro u ⟨z,hz,rfl⟩
    exact modelPhaseMorseInverse_mem (hs' hz)
  have he := intervalIntegral.integral_deriv_smul_comp' hd hc (hg.mono hi)
  simpa only [Function.comp_def,Complex.real_smul] using he.symm

theorem modelPhaseMorse_window_integral
    {χ F : ℝ → ℝ} {σ δ v H : ℝ}
    (hχ : Continuous χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hH : 0 ≤ H)
    (hs : Icc (-H) H ⊆ modelPhaseMorseRange F v) (T : ℝ) :
    (∫ u in modelPhaseMorseInverse F v (-H)..modelPhaseMorseInverse F v H,
      (χ u : ℂ)*(𝐞 (T*F u-(T*v)*u) : ℂ)) =
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
        ∫ z in (-H)..H, (modelPhaseMorseWeight χ F v z : ℂ)*betaQuadraticKernel T z := by
  have hg : ContinuousOn (fun u => (χ u : ℂ)*(𝐞 (T*F u-(T*v)*u) : ℂ)) (Ioo (1 : ℝ) 2) := by
    intro u hu
    have hc := (approximateModelPhase_contDiffAt hF hu).continuousAt
    have he : ContinuousAt (fun u => (χ u : ℂ)*(𝐞 (T*F u-(T*v)*u) : ℂ)) u := by
      simp only [Real.fourierChar_apply]
      fun_prop
    exact he.continuousWithinAt
  rw [integral_inverseMorse_window hσ hδ hF hv hH hs hg,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z hz
  have hz' : z ∈ modelPhaseMorseRange F v := by
    apply hs
    simpa only [uIcc_of_le (by linarith : -H ≤ H)] using hz
  dsimp only
  rw [modelPhaseMorseWeight_eq hz']
  exact modelPhaseMorse_integrand hσ hδ hF hv hz' T

end TaoTrudgianYang2025

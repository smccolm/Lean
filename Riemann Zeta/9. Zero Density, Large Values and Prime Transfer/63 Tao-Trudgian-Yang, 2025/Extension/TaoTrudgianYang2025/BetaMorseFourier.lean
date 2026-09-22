import TaoTrudgianYang2025.BetaMorseAmplitude

/-!
# Exact quadratic representation of the original Poisson Fourier mode

The source is the original cutoff-weighted model integral. The actual
inverse Jacobian retains that cutoff. Integrability and the physical
factor N are proved explicitly; no stationary-phase error is asserted.
-/

noncomputable section

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology FourierTransform

namespace TaoTrudgianYang2025

def modelPhaseMorseWeightedIntegral (χ F : ℝ → ℝ) (T v : ℝ) : ℂ :=
  ∫ z in modelPhaseMorseRange F v,
    (modelPhaseMorseAmplitude χ F v z : ℂ)*(𝐞 (-(T/2)*z^2) : ℂ)

theorem modelPhaseNormalizedIntegrand_integrableOn
    {χ F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ}
    (hχ : Continuous χ) (hF : IsApproximateModelPhaseFunction F σ P δ) (T q : ℝ) :
    IntegrableOn (fun u : ℝ => (χ u : ℂ)*(𝐞 (T*F u-q*u) : ℂ)) (Icc (1 : ℝ) 2) := by
  have hf : ContinuousOn F (Icc (1 : ℝ) 2) := hF.1.continuousOn
  have hp : ContinuousOn (fun u : ℝ => T*F u-q*u) (Icc (1 : ℝ) 2) :=
    (continuousOn_const.mul hf).sub (continuousOn_const.mul continuousOn_id)
  have he : Continuous (fun t : ℝ => (𝐞 t : ℂ)) :=
    continuous_subtype_val.comp Real.continuous_fourierChar
  exact (((Complex.continuous_ofReal.comp hχ).continuousOn).mul
    (he.comp_continuousOn' hp)).integrableOn_Icc

theorem modelPhaseNormalizedIntegrand_support
    {χ F : ℝ → ℝ} (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2) (T q : ℝ) :
    Function.support (fun u : ℝ => (χ u : ℂ)*(𝐞 (T*F u-q*u) : ℂ)) ⊆ Ioo (1 : ℝ) 2 := by
  intro u hu
  by_contra hout
  have hz : χ u = 0 := image_eq_zero_of_notMem_tsupport (fun h => hout (hs h))
  exact hu (by simp only [hz,Complex.ofReal_zero,zero_mul])

theorem modelPhaseNormalizedIntegrand_integrable
    {χ F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ}
    (hχ : Continuous χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (T q : ℝ) :
    Integrable (fun u : ℝ => (χ u : ℂ)*(𝐞 (T*F u-q*u) : ℂ)) := by
  apply (integrableOn_iff_integrable_of_support_subset
    (modelPhaseNormalizedIntegrand_support (F := F) hs T q)).mp
  exact (modelPhaseNormalizedIntegrand_integrableOn hχ hF T q).mono_set Ioo_subset_Icc_self

theorem modelPhaseMorse_integrand
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (T : ℝ) :
    ((deriv (modelPhaseMorseInverse F v) z : ℝ) : ℂ)*
        ((χ (modelPhaseMorseInverse F v z) : ℂ)*
          (𝐞 (T*F (modelPhaseMorseInverse F v z)-(T*v)*modelPhaseMorseInverse F v z) : ℂ)) =
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
        ((modelPhaseMorseAmplitude χ F v z : ℂ)*(𝐞 (-(T/2)*z^2) : ℂ)) := by
  have he : T*F (modelPhaseMorseInverse F v z)-(T*v)*modelPhaseMorseInverse F v z =
      -T*modelPhaseLegendreDual F v + -(T/2)*z^2 := by
    calc
      _ = T*(F (modelPhaseMorseInverse F v z)-v*modelPhaseMorseInverse F v z) := by ring
      _ = T*(-modelPhaseLegendreDual F v-z^2/2) := by
        rw [modelPhaseMorseInverse_quadratic hσ hδ hF hv hz]
      _ = _ := by ring
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul]
  unfold modelPhaseMorseAmplitude
  rw [Complex.ofReal_mul]
  ring

theorem modelPhaseMorseWeightedIntegrand_integrableOn
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : Continuous χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    IntegrableOn (fun z => (modelPhaseMorseAmplitude χ F v z : ℂ)*
      (𝐞 (-(T/2)*z^2) : ℂ)) (modelPhaseMorseRange F v) := by
  have hsource := (modelPhaseNormalizedIntegrand_integrableOn hχ hF T (T*v)).mono_set
    Ioo_subset_Icc_self
  have htrans := (integrableOn_Ioo_iff_morseIntegral hσ hδ hF hv _).mp hsource
  have hs := (modelPhaseMorseRange_isOpen hσ hδ hF hv).measurableSet
  have he : IntegrableOn (fun z => (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
      ((modelPhaseMorseAmplitude χ F v z : ℂ)*(𝐞 (-(T/2)*z^2) : ℂ)))
      (modelPhaseMorseRange F v) :=
    htrans.congr_fun (fun _ hz => modelPhaseMorse_integrand hσ hδ hF hv hz T) hs
  have hunit : IsUnit (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ) :=
    isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp (by simp))
  exact (integrable_const_mul_iff hunit _).mp he

theorem modelPhaseNormalizedMode_morse
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    modelPhaseNormalizedMode χ F T (T*v) =
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*modelPhaseMorseWeightedIntegral χ F T v := by
  have hsource : (∫ u in Ioo (1 : ℝ) 2, (χ u : ℂ)*(𝐞 (T*F u-(T*v)*u) : ℂ)) =
      modelPhaseNormalizedMode χ F T (T*v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz : χ u = 0 := image_eq_zero_of_notMem_tsupport (fun h => hu (hs h))
    simp only [hz,Complex.ofReal_zero,zero_mul]
  rw [← hsource,integral_Ioo_eq_morseIntegral hσ hδ hF hv]
  unfold modelPhaseMorseWeightedIntegral
  rw [← integral_const_mul]
  exact setIntegral_congr_fun (modelPhaseMorseRange_isOpen hσ hδ hF hv).measurableSet
    (fun _ hz => modelPhaseMorse_integrand hσ hδ hF hv hz T)

theorem modelPhaseFourierMode_morse
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhaseFourierMode χ F T N r =
      (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
        modelPhaseMorseWeightedIntegral χ F T (r*N/T) := by
  rw [modelPhaseFourierMode_eq_normalized χ F T r hN,
    modelPhaseStationaryPoint_phase hT hN.ne']
  have hq : r*N = T*(r*N/T) := by field_simp
  have h := modelPhaseNormalizedMode_morse (χ := χ) hs hσ hδ hF hv T
  rw [← hq] at h
  rw [h,Complex.real_smul,mul_assoc]

end TaoTrudgianYang2025

import TaoTrudgianYang2025.SargosPlanarRegularity

/-!
# From the whole-line kernel estimate to actual rectangular windows

The physical factor 16*delta*lambda is derived, not suppressed.
All finite sums, translations and interval integrability are retained.
-/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargosPlanarNormSq_window_le_weighted {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) {δ lambda c d α γ : ℝ}
    (hδ : 0 < δ) (hlambda : 0 < lambda)
    (hα : α ∈ Icc c (c+δ)) (hγ : γ ∈ Icc d (d+lambda)) :
    ‖sargosPlanarSum S z u v α γ‖^2 ≤
      (16*δ*lambda)*sargosWeightedPlanarIntegrand S z u v
        (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ := by
  have hk := sargosSincKernel_window_rectangle hδ hlambda hα hγ
  have hC : 0 < 16*δ*lambda := by positivity
  have h := (div_le_iff₀ hC).mp hk
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖sargosPlanarSum S z u v α γ‖)
  simpa only [sargosWeightedPlanarIntegrand,one_mul,mul_assoc,mul_left_comm,mul_comm] using hm

theorem sargosPlanarNormSq_window_inner_le_weighted {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) {δ lambda c d α : ℝ}
    (hδ : 0 < δ) (hlambda : 0 < lambda) (hα : α ∈ Icc c (c+δ)) :
    (∫ γ in Icc d (d+lambda), ‖sargosPlanarSum S z u v α γ‖^2) ≤
      (16*δ*lambda)*∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v
        (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ := by
  have hi := integrable_sargosWeightedPlanarIntegrand_inner S z u v
    (one_div_pos.mpr hlambda) (1/δ) (c+δ/2) (d+lambda/2) α
  have hC : 0 ≤ 16*δ*lambda := by positivity
  have hn (γ : ℝ) : 0 ≤ sargosWeightedPlanarIntegrand S z u v
      (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ :=
    sargosWeightedPlanarIntegrand_nonneg S z u v
      (by positivity) (by positivity) _ _ _ _
  calc
    _ ≤ ∫ γ in Icc d (d+lambda), (16*δ*lambda)*
        sargosWeightedPlanarIntegrand S z u v
          (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ :=
      setIntegral_mono_on (integrable_sargosPlanarNormSq_window_inner S z u v d lambda α)
        (hi.const_mul (16*δ*lambda)).integrableOn measurableSet_Icc
        (fun γ hγ => sargosPlanarNormSq_window_le_weighted S z u v hδ hlambda hα hγ)
    _ ≤ ∫ γ : ℝ, (16*δ*lambda)*sargosWeightedPlanarIntegrand S z u v
        (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ :=
      setIntegral_le_integral (hi.const_mul (16*δ*lambda))
        (Filter.Eventually.of_forall (fun γ => mul_nonneg hC (hn γ)))
    _ = _ := integral_const_mul _ _

theorem sargosPlanar_window_le_nearPairs {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1)
    {δ lambda : ℝ} (hδ : 0 < δ) (hlambda : 0 < lambda) (c d : ℝ) :
    (∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda),
      ‖sargosPlanarSum S z u v α γ‖^2) ≤
        (16*δ*lambda)*((sargosNearPairs S u v (1/δ) (1/lambda)).card : ℝ) := by
  have hA : 0 < 1/δ := one_div_pos.mpr hδ
  have hB : 0 < 1/lambda := one_div_pos.mpr hlambda
  have hi := integrable_sargosWeightedPlanarIntegrand_outer S z u v hA hB
    (c+δ/2) (d+lambda/2)
  have hC : 0 ≤ 16*δ*lambda := by positivity
  have hn (α : ℝ) : 0 ≤ ∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v
      (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ := by
    apply integral_nonneg
    intro γ
    exact sargosWeightedPlanarIntegrand_nonneg S z u v hA.le hB.le _ _ _ _
  calc
    _ ≤ ∫ α in Icc c (c+δ), (16*δ*lambda)*
        ∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v
          (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ :=
      setIntegral_mono_on (integrable_sargosPlanarNormSq_window_outer S z u v c δ d lambda)
        (hi.const_mul (16*δ*lambda)).integrableOn measurableSet_Icc
        (fun α hα => sargosPlanarNormSq_window_inner_le_weighted S z u v hδ hlambda hα)
    _ ≤ ∫ α : ℝ, (16*δ*lambda)*∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v
        (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ :=
      setIntegral_le_integral (hi.const_mul (16*δ*lambda))
        (Filter.Eventually.of_forall (fun α => mul_nonneg hC (hn α)))
    _ = (16*δ*lambda)*(∫ α : ℝ, ∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v
        (1/δ) (1/lambda) (c+δ/2) (d+lambda/2) α γ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sargosWeightedPlanarIntegral_le_nearPairs S z u v hz hA hB (c+δ/2) (d+lambda/2)) hC

end TaoTrudgianYang2025

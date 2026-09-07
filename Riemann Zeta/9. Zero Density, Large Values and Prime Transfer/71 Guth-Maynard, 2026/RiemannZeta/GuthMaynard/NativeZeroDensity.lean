import RiemannZeta.GuthMaynard.ArithmeticCoefficients
import RiemannZeta.GuthMaynard.BetaDependence
import RiemannZeta.GuthMaynard.ClassicalDensity
import RiemannZeta.GuthMaynard.ClassicalEndpointDensity
import RiemannZeta.GuthMaynard.HughesYoungNativeCompletion
import RiemannZeta.GuthMaynard.LargeValuesFinal
import RiemannZeta.GuthMaynard.MeanValueProof
import RiemannZeta.GuthMaynard.Transfer
import RiemannZeta.GuthMaynard.TypeIICoverage

namespace RiemannZeta.GuthMaynard

/-!
# Native zero-density integration

This module closes the inclusive classical endpoints and then specializes the
primitive-input Section 13.1 transfer to the native analytic inputs.  The
interior classical cases pass through the multiplicity-weighted positive-slab
theorems and `dyadicToGlobalZeroCount`; the boundary cases use the separately
proved exact endpoint theorems.
-/

/-- The full native Ingham zero-density estimate, including both endpoints. -/
theorem ingham_zero_density_native :
    InghamZeroDensity (fun σ T => N σ T) := by
  intro σ hσLower hσUpper
  rcases hσLower.eq_or_lt with hσHalf | hσLower
  · subst σ
    exact ingham_zero_density_at_half_native
  rcases hσUpper.eq_or_lt with hσOne | hσUpper
  · subst σ
    exact ingham_zero_density_at_one_native
  · have hExponentNonneg : 0 ≤ 3 * (1 - σ) / (2 - σ) := by
      exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hσUpper.le)) (by linarith)
    exact dyadicToGlobalZeroCount σ (3 * (1 - σ) / (2 - σ)) hExponentNonneg
      (ingham_endpoint_positive_slab_native hσLower hσUpper)

/-- The full native Huxley zero-density estimate, including both endpoints. -/
theorem huxley_zero_density_native :
    HuxleyZeroDensity (fun σ T => N σ T) := by
  intro σ hσLower hσUpper
  rcases hσLower.eq_or_lt with hσThreeQuarters | hσLower
  · subst σ
    exact huxley_zero_density_at_three_quarters_of_ingham ingham_zero_density_native
  rcases hσUpper.eq_or_lt with hσOne | hσUpper
  · subst σ
    exact huxley_zero_density_at_one_native
  · have hExponentNonneg : 0 ≤ 3 * (1 - σ) / (3 * σ - 1) := by
      exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hσUpper.le)) (by linarith)
    exact dyadicToGlobalZeroCount σ (3 * (1 - σ) / (3 * σ - 1)) hExponentNonneg
      (huxley_endpoint_positive_slab_native hσLower hσUpper)

/-- Goal C: after supplying the Guth--Maynard large-values theorem, every
remaining analytic input to Section 13.1 is discharged by a native theorem. -/
theorem guthMaynardZeroDensity_of_largeValues_native
    (hLargeValues : GuthMaynardLargeValues) :
    GuthMaynardZeroDensity (fun σ T => N σ T) :=
  conditionalZeroDensityTransfer
    hLargeValues
    montgomery_mean_value_native
    beta_dependence_removal
    localZeroMultiplicityBound_native
    divisorCountBound_native
    factorizationCountBound_native
    typeIContourTypeIICover_native
    typeIIFourthMomentReduction_native
    twistedZetaFourthMoment_native
    huxley_zero_density_native

/-- The concrete native Guth--Maynard zero-density estimate. -/
theorem guthMaynardZeroDensity_native :
    GuthMaynardZeroDensity (fun σ T => N σ T) :=
  guthMaynardZeroDensity_of_largeValues_native guthMaynardLargeValues_native

/-- The concrete combined Ingham/Guth--Maynard zero-density estimate. -/
theorem combined_zero_density_native :
    CombinedZeroDensity (fun σ T => N σ T) :=
  combined_zero_density_transfer_native
    (fun σ T => N σ T)
    ingham_zero_density_native
    guthMaynardZeroDensity_native

end RiemannZeta.GuthMaynard

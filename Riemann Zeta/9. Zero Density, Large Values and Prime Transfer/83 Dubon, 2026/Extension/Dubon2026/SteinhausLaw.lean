import Dubon2026.CircleRadial
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # The actual finite sum of independent Haar circle coordinates and its law -/

namespace Dubon2026

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Independent normalized Haar circle coordinates on a finite product. -/
def steinhausHaar (ι : Type*) [Fintype ι] : Measure (ι → UnitAddCircle) :=
  Measure.pi (fun _ : ι => AddCircle.haarAddCircle)

instance steinhausHaar_isProbabilityMeasure : IsProbabilityMeasure (steinhausHaar ι) := by
  unfold steinhausHaar
  infer_instance

/-- The literal weighted sum of the unit-circle coordinates. -/
def steinhausSum (c : ι → ℝ) (z : ι → UnitAddCircle) : ℂ :=
  ∑ i, (c i : ℂ) * fourier 1 (z i)

theorem continuous_steinhausSum (c : ι → ℝ) : Continuous (steinhausSum c) := by
  unfold steinhausSum
  fun_prop

/-- The probability distribution of the genuine finite sum. -/
def steinhausLaw (c : ι → ℝ) : Measure ℂ := (steinhausHaar ι).map (steinhausSum c)

instance steinhausLaw_isProbabilityMeasure (c : ι → ℝ) : IsProbabilityMeasure (steinhausLaw c) :=
  Measure.isProbabilityMeasure_map (continuous_steinhausSum c).measurable.aemeasurable

theorem steinhaus_exp_sum_eq_prod (c : ι → ℝ) (ξ : ℂ) (z : ι → UnitAddCircle) :
    Complex.exp (Complex.I * (((conj ξ * steinhausSum c z).re : ℝ) : ℂ)) =
      ∏ i, Complex.exp (Complex.I * (((conj ξ * ((c i : ℂ) * fourier 1 (z i))).re : ℝ) : ℂ)) := by
  simp only [steinhausSum, Finset.mul_sum, Complex.re_sum, Complex.ofReal_sum,
    Complex.exp_sum]

theorem integral_steinhaus_characteristic (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ξ : ℂ) :
    (∫ z : ι → UnitAddCircle, Complex.exp
      (Complex.I * (((conj ξ * steinhausSum c z).re : ℝ) : ℂ)) ∂steinhausHaar ι) =
      ∏ i, (besselJ0 (c i * ‖ξ‖) : ℂ) := by
  simp_rw [steinhaus_exp_sum_eq_prod]
  rw [steinhausHaar, integral_fintype_prod_eq_prod (fun i (z : UnitAddCircle) =>
    Complex.exp (Complex.I * (((conj ξ * ((c i : ℂ) * fourier 1 z)).re : ℝ) : ℂ)))]
  apply Finset.prod_congr rfl
  intro i _
  exact circle_radial_characteristic ξ (hc i)

theorem charFun_steinhausLaw (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ξ : ℂ) :
    charFun (steinhausLaw c) ξ = ∏ i, (besselJ0 (c i * ‖ξ‖) : ℂ) := by
  rw [charFun_apply, steinhausLaw, integral_map
    (continuous_steinhausSum c).measurable.aemeasurable (by fun_prop)]
  have he (x : ℂ) : inner ℝ x ξ = (conj ξ * x).re := by
    rw [real_inner_comm, Complex.inner, mul_comm]
  simp_rw [he, mul_comm _ Complex.I]
  exact integral_steinhaus_characteristic c hc ξ

theorem norm_charFun_steinhausLaw (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ξ : ℂ) :
    ‖charFun (steinhausLaw c) ξ‖ = ∏ i, |besselJ0 (c i * ‖ξ‖)| := by
  rw [charFun_steinhausLaw c hc]
  simp only [norm_prod, Complex.norm_real, Real.norm_eq_abs]

end

end Dubon2026

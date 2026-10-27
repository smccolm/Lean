import Dubon2026.SourceBoundedIntegralSeriesProduct
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> rational Fourier denominators. For rational series,
one uniform integral bound gives a literal integer power series after
scaling, using normality of the integers in the rationals coefficientwise. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem HasBoundedIntegralCoefficients.exists_integer_series
    {f : PowerSeries ℚ} (hf : HasBoundedIntegralCoefficients f) :
    ∃ d : ℤ, ∃ F : PowerSeries ℤ, d ≠ 0 ∧
      F.map (algebraMap ℤ ℚ) = PowerSeries.C (d : ℚ) * f := by
  classical
  obtain ⟨d, hd, hi⟩ := hf
  choose z hz using fun n => IsIntegrallyClosed.algebraMap_eq_of_integral (hi n)
  refine ⟨d, PowerSeries.mk z, hd, ?_⟩
  apply PowerSeries.ext
  intro n
  simpa only [PowerSeries.coeff_map, PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul] using hz n

end
end Dubon2026.SourceFunctionField

import Dubon2026.SourceWeierstrassIntegralDenominator
import Dubon2026.SourceIntegralEisensteinSix
import Dubon2026.SourceBoundedIntegralSeriesConstant

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded coefficients of original Fricke numerators.
The literal E4 E6 series is integral at width N; multiply it by the already
proved uniformly scaled torsion series and the actual Fricke factor -1/2592.
No analytic expansion, level object or coefficient family is substituted. -/
namespace Dubon2026.SourceFricke
noncomputable section
open SourceFunctionField

/-- The integral width-N series of the original E4 E6 product. -/
def e4e6IntegerSeries (N : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if N ∣ n then (eisenstein4 * eisenstein6).coeff (n / N) else 0

theorem e4e6QSeries_eq_integer_map (N : ℕ) :
    e4e6QSeries N = (e4e6IntegerSeries N).map (Int.castRingHom ℚ) := by
  ext n
  rw [PowerSeries.coeff_map, e4e6QSeries, e4e6IntegerSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs
  · rw [eisensteinQSeries_four_eq_integer_map, eisensteinQSeries_six_eq_integer_map,
      ← map_mul, PowerSeries.coeff_map]
  · exact (map_zero _).symm

theorem e4e6QSeriesK_coeff_isIntegral (N n : ℕ) :
    IsIntegral ℤ (((e4e6QSeries N).map (algebraMap ℚ (kN N))).coeff n) := by
  rw [e4e6QSeries_eq_integer_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  simp only [Int.coe_castRingHom, map_intCast]
  exact isIntegral_algebraMap (x := (e4e6IntegerSeries N).coeff n)

theorem hasBoundedIntegralCoefficients_frickeHQSeriesK {N a₁ : ℕ} [NeZero N]
    (ha₁ : a₁ < N) (a₂ : ℕ) : HasBoundedIntegralCoefficients (frickeHQSeriesK ha₁ a₂) := by
  obtain ⟨d, hd, hi⟩ := exists_wpQSeriesK_integral_multiple ha₁ a₂
  exact (hasBoundedIntegralCoefficients_of_integral (e4e6QSeriesK_coeff_isIntegral N)).mul
    ⟨d, ne_of_gt hd, hi⟩

theorem hasBoundedIntegralCoefficients_frickeNumerator {N : ℕ} [NeZero N]
    (i : FrickeIdx N) : HasBoundedIntegralCoefficients
      (PowerSeries.C (-1 / 2592 : kN N) *
        frickeHQSeriesK (frickeIdx_hyps i.1 i.2).1 (i.1 1).val) := by
  have hc : HasBoundedIntegralCoefficients (PowerSeries.C (-1 / 2592 : kN N)) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] using
      hasBoundedIntegralCoefficients_C_rat (kN N) (-1 / 2592)
  exact hc.mul (hasBoundedIntegralCoefficients_frickeHQSeriesK _ _)

end
end Dubon2026.SourceFricke

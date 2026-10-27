import Dubon2026.SourceEisensteinRationalSeries
import Dubon2026.SourceEisensteinFourExpansion

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> integral Eisenstein factors. Reuse the original
integer E4 series. The exact normalized E6 coefficient formula supplies its
integer series, needed for the Fricke numerator and later unit cancellation. -/
namespace Dubon2026.SourceFricke
noncomputable section
open SourceFunctionField UpperHalfPlane ModularForm
open scoped ModularForm

/-- The integer series of the actual normalized weight-six Eisenstein form. -/
def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ)

theorem constantCoeff_eisenstein6 : PowerSeries.constantCoeff eisenstein6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, eisenstein6, PowerSeries.coeff_mk]
  simp

theorem eisensteinQSeries_four_eq_integer_map :
    eisensteinQSeries 4 = eisenstein4.map (Int.castRingHom ℚ) := by
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  rw [eisensteinQSeries_map (by norm_num) (by decide), qExpansion_E4_eq_map_eisenstein4]
  ext n
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom, map_intCast]

theorem eisensteinQSeries_six_eq_integer_map :
    eisensteinQSeries 6 = eisenstein6.map (Int.castRingHom ℚ) := by
  have h6 : bernoulli 6 = (1 / 42 : ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, Nat.choose]
    have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
    rw [h5]
    norm_num
  ext n
  rw [PowerSeries.coeff_map, eisensteinQSeries, eisenstein6, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, h6]
  split_ifs <;> simp only [Int.coe_castRingHom] <;> push_cast <;> ring

end
end Dubon2026.SourceFricke

import Dubon2026.SourceIntegralPowerSeriesFrobenius
import Dubon2026.SourceHasseCoefficientTransport

/-! DUB-17/18 -> original Frobenius quadratic relation -> geometric
versus arithmetic Frobenius. The existing power-series expansion theorem
and coefficient transport, combined with the native Laurent decomposition,
give the exact pth-power formula needed for the actual modular field.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_FrobeniusModL.lean, KeyLemma section. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

theorem pow_char_single_one_eq (n : ℤ) :
    (HahnSeries.single n (1 : R)) ^ p =
      coeffMap (frobenius R p) (qExpand R p (HahnSeries.single n (1 : R))) := by
  rw [HahnSeries.single_pow, one_pow,
    show (p • n : ℤ) = (p : ℤ) * n from nsmul_eq_mul p n,
    qExpand_single, coeffMap_single, show frobenius R p 1 = 1 from map_one _]

theorem pow_char_ofPowerSeries_eq (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u) ^ p =
      coeffMap (frobenius R p) (qExpand R p (HahnSeries.ofPowerSeries ℤ R u)) := by
  haveI : ExpChar R p := ExpChar.prime (Fact.out : p.Prime)
  rw [qExpand_ofPowerSeries_eq_expand p u, coeffMap_ofPowerSeries, ← map_pow]
  congr 1
  exact (MvPowerSeries.map_frobenius_expand p (NeZero.ne p) (f := u)).symm

theorem pow_char_eq_coeffMap_frobenius_qExpand (s : LaurentSeries R) :
    s ^ p = coeffMap (frobenius R p) (qExpand R p s) := by
  conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  conv_rhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  rw [mul_pow, map_mul, map_mul, pow_char_single_one_eq p s.order]
  congr 1
  exact pow_char_ofPowerSeries_eq p s.powerSeriesPart

end
end Dubon2026.SourceFunctionField

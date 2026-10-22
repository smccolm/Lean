import Dubon2026.SourceCuspTaylorLaurentSubstitution
import Dubon2026.SourceLaurentOrderValuation
import Mathlib.Analysis.Meromorphic.Order

/-! DUB-17/18 -> original torsion cardinality -> cusp parameters.
The first nonzero Taylor coefficient gives both the analytic order and
the order of the actual Laurent series. Hence analytic quotients have
exactly the order of their formal Laurent quotient. This supplies the
order comparison needed by the original cusp embedding consumer.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section

theorem order_series {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    (series f).order = analyticOrderAt f 0 := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  constructor
  · intro hn i hi
    have hc := PowerSeries.coeff_of_lt_order i
      (lt_of_lt_of_le (show (i : ℕ∞) < n by exact_mod_cast hi) hn)
    simpa only [coeff_series, div_eq_zero_iff, Nat.cast_eq_zero,
      Nat.factorial_ne_zero, or_false] using hc
  · intro hn
    apply PowerSeries.nat_le_order
    intro i hi
    rw [coeff_series, hn i hi, zero_div]

theorem order_coe_series {f : ℂ → ℂ} (hf0 : series f ≠ 0) :
    (series f : LaurentSeries ℂ).order = ((series f).order.toNat : ℤ) := by
  have hc0 : (series f : LaurentSeries ℂ) ≠ 0 :=
    fun h => hf0 (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact PowerSeries.coeff_order hf0
  · apply (HahnSeries.le_order_iff_forall hc0).mpr
    intro j hj
    rcases le_or_gt 0 j with hj0 | hj0
    · lift j to ℕ using hj0
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      exact PowerSeries.coeff_of_lt_order_toNat _ (by exact_mod_cast hj)
    · exact ofPowerSeries_coeff_of_neg _ hj0

theorem meromorphicOrderAt_eq_series_order {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : series f ≠ 0) :
    meromorphicOrderAt f 0 = ((series f : LaurentSeries ℂ).order : WithTop ℤ) := by
  rw [hf.meromorphicOrderAt_eq, ← order_series hf, order_coe_series hf0,
    ← PowerSeries.coe_toNat_order hf0, ENat.map_coe, ENat.toNat_coe]

theorem meromorphicOrderAt_quotient {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : series f ≠ 0) (hg0 : series g ≠ 0) :
    meromorphicOrderAt (f / g) 0 =
      (((series f : LaurentSeries ℂ) / (series g : LaurentSeries ℂ)).order : WithTop ℤ) := by
  have hfc : (series f : LaurentSeries ℂ) ≠ 0 :=
    fun h => hf0 (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  have hgc : (series g : LaurentSeries ℂ) ≠ 0 :=
    fun h => hg0 (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  rw [meromorphicOrderAt_div hf.meromorphicAt hg.meromorphicAt,
    meromorphicOrderAt_eq_series_order hf hf0, meromorphicOrderAt_eq_series_order hg hg0,
    div_eq_mul_inv, HahnSeries.order_mul hfc (inv_ne_zero hgc), laurent_order_inv]
  change ((series f : LaurentSeries ℂ).order : WithTop ℤ) -
    ((series g : LaurentSeries ℂ).order : WithTop ℤ) = _
  rw [← sub_eq_add_neg]
  rfl

end
end Dubon2026.SourceFunctionField.CuspTaylor

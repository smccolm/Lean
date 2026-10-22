import Dubon2026.SourceTaylorSubstitutions
import Dubon2026.SourceLaurentRootTwist
import Dubon2026.SourceModularJSeries

/-! DUB-17/18 -> original torsion cardinality -> actual cusp germs.
Identify the exact Laurent twist/expansion maps already used by the
original cusp embeddings with the corresponding Taylor substitutions.
All integral coefficients, including negative indices, are retained.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section

theorem qTwist_coe_powerSeries (u : ℂˣ) (P : PowerSeries ℂ) :
    qTwist u (P : LaurentSeries ℂ) = (PowerSeries.rescale (u : ℂ) P : LaurentSeries ℂ) := by
  ext n
  rw [qTwist_coeff]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_rescale, zpow_natCast, Units.val_pow_eq_pow_val]
  · rw [ofPowerSeries_coeff_of_neg _ (lt_of_not_ge hn),
      ofPowerSeries_coeff_of_neg _ (lt_of_not_ge hn), mul_zero]

theorem qExpand_coe_powerSeries (d : ℕ) [NeZero d] (P : PowerSeries ℂ) :
    qExpand ℂ d (P : LaurentSeries ℂ) = (PowerSeries.expand d (NeZero.ne d) P : LaurentSeries ℂ) := by
  ext n
  by_cases hd : (d : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [qExpand_coeff_mul]
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      rw [← Nat.cast_mul, HahnSeries.ofPowerSeries_apply_coeff,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_expand_mul]
    · rw [ofPowerSeries_coeff_of_neg _ (lt_of_not_ge hm),
        ofPowerSeries_coeff_of_neg _ (mul_neg_of_pos_of_neg
          (by exact_mod_cast Nat.pos_of_neZero d) (lt_of_not_ge hm))]
  · rw [qExpand_coeff_of_not_dvd d _ hd]
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_of_not_dvd d (NeZero.ne d) P
          (fun hdn => hd (Int.natCast_dvd_natCast.mpr hdn))]
    · exact (ofPowerSeries_coeff_of_neg _ hn).symm

theorem qTwist_series (u : ℂˣ) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    qTwist u (series f : LaurentSeries ℂ) = (series (fun z => f (u * z)) : LaurentSeries ℂ) := by
  rw [qTwist_coe_powerSeries, series_comp_mul hf]

theorem qExpand_series (d : ℕ) [NeZero d] {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    qExpand ℂ d (series f : LaurentSeries ℂ) = (series (fun z => f (z ^ d)) : LaurentSeries ℂ) := by
  rw [qExpand_coe_powerSeries, series_comp_pow hf d (NeZero.ne d)]

end
end Dubon2026.SourceFunctionField.CuspTaylor

import Dubon2026.SourceGammaOneModularStretchCoefficients
import Dubon2026.SourceOriginalHeckeDegeneracy

/-! DUB-17/18 -> all-weight original adic association -> arithmetic Gamma1
realization -> genuine geometric Hecke maps. Native power-series expansion
and the existing Laurent substitution give the actual second field inclusion.
No alternate branch or assumed field-preservation predicate is introduced. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup IntermediateField
open scoped MatrixGroups

theorem intSeriesC_expand (K : Type*) [Field K] (d : ℕ) [NeZero d]
    (p : PowerSeries ℤ) :
    intSeriesC K (PowerSeries.expand d (NeZero.ne d) p) =
      qExpand K d (intSeriesC K p) := by
  ext n
  by_cases hd : (d : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [qExpand_coeff_mul]
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      simp only [intSeriesC, ← Nat.cast_mul, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map, PowerSeries.coeff_expand_mul]
    · simp only [intSeriesC]
      rw [ofPowerSeries_coeff_of_neg _ (mul_neg_of_pos_of_neg
        (by exact_mod_cast Nat.pos_of_neZero d) (lt_of_not_ge hm)),
        ofPowerSeries_coeff_of_neg _ (lt_of_not_ge hm)]
  · rw [qExpand_coeff_of_not_dvd d _ hd]
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
      rw [PowerSeries.coeff_expand_of_not_dvd _ _ _
        (fun hdn => hd (Int.natCast_dvd_natCast.mpr hdn)), map_zero]
    · exact ofPowerSeries_coeff_of_neg _ hn

theorem qExpand_intFormRatiosC (K : Type*) [Field K] (M d : ℕ) [NeZero d]
    {x : LaurentSeries K} (hx : x ∈ intFormRatiosC K (Gamma1 M)) :
    qExpand K d x ∈ intFormRatiosC K (Gamma1 M ⊓ Gamma0 (d * M)) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  refine ⟨k, modularStretch M d f, modularStretch M d g,
    PowerSeries.expand d (NeZero.ne d) pf, PowerSeries.expand d (NeZero.ne d) pg,
    modularStretch_integral M d f hf, modularStretch_integral M d g hg, ?_, ?_⟩
  · rw [intSeriesC_expand]
    exact (map_ne_zero (qExpand K d)).mpr hg0
  · rw [map_div₀, intSeriesC_expand, intSeriesC_expand]

theorem gamma1_degeneracy_map_le (K : Type*) [Field K] (M d : ℕ) [NeZero d] :
    (x1FunctionFieldC K M).map (qExpandAlgHom K d) ≤
      x1x0FunctionFieldC K M (d * M) := by
  change (adjoin K (intFormRatiosC K (Gamma1 M))).map _ ≤ _
  rw [adjoin_map, adjoin_le_iff]
  rintro x ⟨y, hy, rfl⟩
  exact intFormRatiosC_subset K _ (qExpand_intFormRatiosC K M d hy)

end
end Dubon2026.SourceFunctionField.GammaOne

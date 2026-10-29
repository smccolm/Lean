import Dubon2026.SourceGammaOneIntegralJRatio
import Dubon2026.SourceLaurentEuler

/-! DUB-17/18 -> original Gamma1 degree preservation -> finite reduced
coordinate degree transport. Literal coefficient maps preserve integer
Fourier series and the original adjoined integral-ratio field. This supplies
the actual map from the prime-field action to the native residue field.
Adapted from the pinned Apache-2.0 FLT coefficient-map proof at
6e837e75355538c7f80bab5b956861e86c4eacc2. Only inclusion is needed; a new
general base-change equality is unnecessary for the required degree bound. -/
namespace Dubon2026.SourceFunctionField.ReducedDegreeTransport
noncomputable section
open IntermediateField GammaOne
open scoped MatrixGroups

theorem coeffMap_intSeries {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (p : PowerSeries ℤ) :
    coeffMap σ (intSeriesC K p) = intSeriesC L p := by
  ext n
  rw [coeffMap_coeff]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
    exact map_intCast σ _
  · have hn' : n < 0 := lt_of_not_ge hn
    rw [intSeriesC, intSeriesC, ofPowerSeries_coeff_of_neg _ hn',
      ofPowerSeries_coeff_of_neg _ hn', map_zero]

theorem coeffMap_mem_originalField {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (Γ : Subgroup SL(2, ℤ)) {x : LaurentSeries K}
    (hx : x ∈ qExpFunctionFieldC K Γ) : coeffMap σ x ∈ qExpFunctionFieldC L Γ := by
  let T := (qExpFunctionFieldC L Γ).toSubfield.comap (coeffMap σ)
  have hgen : intFormRatiosC K Γ ⊆ (T : Set (LaurentSeries K)) := by
    rintro y ⟨k, f, g, p, q, hp, hq, hq0, rfl⟩
    change coeffMap σ (intSeriesC K p / intSeriesC K q) ∈ qExpFunctionFieldC L Γ
    rw [map_div₀, coeffMap_intSeries, coeffMap_intSeries]
    refine div_mem_qExpFunctionFieldC f g hp hq ?_
    rw [← coeffMap_intSeries σ]
    exact fun h => hq0 ((coeffMap σ).injective (h.trans (map_zero _).symm))
  have hconst : Set.range (algebraMap K (LaurentSeries K)) ⊆ (T : Set (LaurentSeries K)) := by
    rintro y ⟨c, rfl⟩
    change coeffMap σ (algebraMap K (LaurentSeries K) c) ∈ qExpFunctionFieldC L Γ
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single,
      ← SourceDifferential.algebraMap_laurentSeries_apply_alt]
    exact (qExpFunctionFieldC L Γ).algebraMap_mem _
  have hle : (qExpFunctionFieldC K Γ).toSubfield ≤ T := by
    rw [qExpFunctionFieldC, adjoin_toSubfield]
    exact Subfield.closure_le.mpr (Set.union_subset hconst hgen)
  exact hle hx

end
end Dubon2026.SourceFunctionField.ReducedDegreeTransport

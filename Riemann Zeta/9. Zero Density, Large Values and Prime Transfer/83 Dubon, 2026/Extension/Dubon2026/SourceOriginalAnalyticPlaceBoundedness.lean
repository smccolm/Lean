import Dubon2026.SourceOriginalAnalyticPlaces

/-! DUB-17/18 -> analytic regular-differential realization -> the
analytic-place membership dictionary. The actual normalized place contains
exactly those original functions whose meromorphic realizations are bounded
on a punctured neighborhood. Native meromorphic limit/pole criteria prove
both directions; no boundedness dictionary is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology

theorem isBoundedUnder_nhdsNE_coe_iff {u : ℍ → ℝ} {τ : ℍ} :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] (τ : ℂ)) (fun z : ℂ => u (ofComplex z)) ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) u := by
  rw [← ModularRatios.map_coe_nhdsNE, Filter.isBoundedUnder_map_iff]
  simp only [Function.comp_def, ofComplex_apply]

theorem originalAnalyticOrder_nonneg_iff_bounded (N : ℕ) [NeZero N]
    (τ : ℍ) (x : modularFunctionFieldOver N ℂ) :
    0 ≤ originalAnalyticOrder N τ x ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize N (x : LaurentSeries ℂ) z‖) := by
  rw [← isBoundedUnder_nhdsNE_coe_iff, originalAnalyticOrder,
    ← tendsto_nhds_iff_meromorphicOrderAt_nonneg (meromorphicAt_original_realize N x τ)]
  constructor
  · rintro ⟨c, hc⟩
    exact hc.norm.isBoundedUnder_le
  · intro hb
    by_contra hn
    have hneg : meromorphicOrderAt
        (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) < 0 := by
      rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg (meromorphicAt_original_realize N x τ), not_le] at hn
      exact hn
    have hcob := (tendsto_cobounded_iff_meromorphicOrderAt_neg (meromorphicAt_original_realize N x τ)).mpr hneg
    rw [← tendsto_norm_atTop_iff_cobounded] at hcob
    exact Filter.not_isBoundedUnder_of_tendsto_atTop hcob hb

theorem originalAnalyticPlace_mem_iff_bounded (N : ℕ) [NeZero N]
    (τ : ℍ) (x : modularFunctionFieldOver N ℂ) :
    x ∈ (originalAnalyticPlace N τ).toValuationSubring ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize N (x : LaurentSeries ℂ) z‖) := by
  rw [originalAnalyticPlace_mem_iff, originalAnalyticOrder_nonneg_iff_bounded]

end
end Dubon2026.SourceFunctionField

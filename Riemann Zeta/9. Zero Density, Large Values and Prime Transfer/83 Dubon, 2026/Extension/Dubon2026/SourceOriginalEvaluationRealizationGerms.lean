import Dubon2026.SourceOriginalAnalyticEvaluation

/-! DUB-17/18 -> original Picard-period Hecke comparison -> differential
pullback. The actual residue evaluation and the original analytic
realization agree on every punctured germ. This follows from the proved
residue limit at nearby regular points, not a supplied comparison map.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem originalPlaceEval_eq_realize_of_analyticAt
    (f : modularFunctionFieldOver N ℂ) (τ : ℍ)
    (ha : AnalyticAt ℂ (fun z : ℂ => realize N (f : LaurentSeries ℂ) (ofComplex z))
      (τ : ℂ)) :
    originalPlaceEval N ℂ (originalAnalyticPlace N τ) f =
      realize N (f : LaurentSeries ℂ) τ := by
  have hf : f ∈ (originalAnalyticPlace N τ).toValuationSubring :=
    (originalAnalyticPlace_mem_iff N τ f).mpr ha.meromorphicOrderAt_nonneg
  have h := tendsto_nhds_unique (original_realize_tendsto_residue N τ f hf)
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [ofComplex_apply] using h

theorem originalPlaceEval_eventuallyEq_realize
    (f : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    (fun z : ℂ => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex z)) f) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => realize N (f : LaurentSeries ℂ) (ofComplex z) := by
  filter_upwards [(meromorphicAt_original_realize N f τ).eventually_analyticAt,
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z ha hz
  have h := originalPlaceEval_eq_realize_of_analyticAt N f ⟨z, hz⟩ ha
  simpa only [ofComplex_apply_of_im_pos hz] using h

end
end Dubon2026.SourceFunctionField

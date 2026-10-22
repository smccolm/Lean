import Dubon2026.SourceOriginalPlaceEvaluation
import Dubon2026.SourceOriginalAnalyticPlaces
import Mathlib.Analysis.Meromorphic.NormalForm

/-! DUB-17/18 -> original torsion cardinality -> complex Abel--Jacobi
comparison -> charts with exact original place orders. The existing
meromorphic realization already avoids reconstructing convergence of
arbitrary algebraic power series. Its regular limit is proved equal to
the literal original residue evaluation, and native meromorphic normal
form supplies a holomorphic representative with that value. This closes
the value comparison required by local uniformizer charts; construction
of the charts and the global Abel--Jacobi comparison remain required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology

theorem original_realize_sub_constant_eventuallyEq (N : ℕ) [NeZero N]
    (f : modularFunctionFieldOver N ℂ) (c : ℂ) (τ : ℍ) :
    (fun z : ℂ => realize N
      ((f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c : modularFunctionFieldOver N ℂ) :
        LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => realize N (f : LaurentSeries ℂ) (ofComplex z) - c := by
  have he : f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c =
      f + algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c) := by
    rw [map_neg, sub_eq_add_neg]
  rw [he]
  filter_upwards [original_realize_add_eventuallyEq N f
    (algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c)) τ] with z hz
  have hconst : realize N
      ((algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c) : modularFunctionFieldOver N ℂ) :
        LaurentSeries ℂ) (ofComplex z) = -c := realize_algebraMap N (-c) (ofComplex z)
  simpa only [Pi.add_apply, hconst, sub_eq_add_neg] using hz

theorem original_realize_tendsto_residue (N : ℕ) [NeZero N] (τ : ℍ)
    (f : modularFunctionFieldOver N ℂ)
    (hf : f ∈ (originalAnalyticPlace N τ).toValuationSubring) :
    Tendsto (fun z : ℂ => realize N (f : LaurentSeries ℂ) (ofComplex z))
      (𝓝[≠] (τ : ℂ)) (𝓝 (originalPlaceEval N ℂ (originalAnalyticPlace N τ) f)) := by
  let v := originalAnalyticPlace N τ
  let c := originalPlaceEval N ℂ v f
  by_cases hc : f = algebraMap ℂ (modularFunctionFieldOver N ℂ) c
  · change Tendsto _ _ (𝓝 c)
    have he : (fun z : ℂ => realize N (f : LaurentSeries ℂ) (ofComplex z)) = fun _ => c := by
      funext z
      rw [hc]
      exact realize_algebraMap N c (ofComplex z)
    rw [he]
    exact tendsto_const_nhds
  · have hne : f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c ≠ 0 := sub_ne_zero.mpr hc
    have hz : originalPlaceEval N ℂ v (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) = 0 := by
      rw [originalPlaceEval_sub_algebraMap N ℂ v hf]
      exact sub_self c
    have ho := (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v
      (sub_mem hf (v.algebraMap_mem' c)) hne).mp hz
    have hp : 0 < originalAnalyticOrder N τ
        (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) := by
      rw [originalAnalyticPlace_order N τ _ hne]
      exact WithTop.coe_pos.mpr (mul_pos
        (Int.natCast_pos.mpr (originalAnalyticRamification_pos N τ)) ho)
    have hlim := (tendsto_zero_of_meromorphicOrderAt_pos hp).congr'
      (original_realize_sub_constant_eventuallyEq N f c τ)
    have h := hlim.add_const c
    simpa only [sub_add_cancel, zero_add] using h

theorem original_regular_analytic_representative (N : ℕ) [NeZero N] (τ : ℍ)
    (f : modularFunctionFieldOver N ℂ)
    (hf : f ∈ (originalAnalyticPlace N τ).toValuationSubring) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      g τ = originalPlaceEval N ℂ (originalAnalyticPlace N τ) f ∧
      g =ᶠ[𝓝[≠] (τ : ℂ)] (fun z => realize N (f : LaurentSeries ℂ) (ofComplex z)) := by
  let F : ℂ → ℂ := fun z => realize N (f : LaurentSeries ℂ) (ofComplex z)
  have hm : MeromorphicAt F (τ : ℂ) := meromorphicAt_original_realize N f τ
  let g := toMeromorphicNFAt F (τ : ℂ)
  have he : F =ᶠ[𝓝[≠] (τ : ℂ)] g := hm.eq_nhdsNE_toMeromorphicNFAt
  have ha : AnalyticAt ℂ g (τ : ℂ) := by
    apply meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [← meromorphicOrderAt_congr he]
    exact (originalAnalyticPlace_mem_iff N τ f).mp hf
  refine ⟨g, ha, ?_, he.symm⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (original_realize_tendsto_residue N τ f hf) he.symm

end
end Dubon2026.SourceFunctionField

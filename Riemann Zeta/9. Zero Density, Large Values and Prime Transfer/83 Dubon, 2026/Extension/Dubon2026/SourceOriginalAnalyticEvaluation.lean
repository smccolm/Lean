import Dubon2026.SourceOriginalAnalyticResidueValues

/-! DUB-17/18 -> original torsion cardinality -> complex Abel--Jacobi
comparison -> charts on the original places. The literal residue-value
function, including value zero at poles, is the native meromorphic normal
form of the already proved original realization. Consequently it is
analytic exactly at regular places, and its analytic order equals the
same original normalized order times the proved ramification. These are
actual evaluation functions, not separately supplied analytic models.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology

private theorem eval_eq_normalForm (N : ℕ) [NeZero N]
    (f : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    originalPlaceEval N ℂ (originalAnalyticPlace N τ) f =
      toMeromorphicNFAt (fun z : ℂ => realize N (f : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) τ := by
  let F : ℂ → ℂ := fun z => realize N (f : LaurentSeries ℂ) (ofComplex z)
  have hm : MeromorphicAt F (τ : ℂ) := meromorphicAt_original_realize N f τ
  have hn : MeromorphicNFAt (toMeromorphicNFAt F (τ : ℂ)) (τ : ℂ) :=
    meromorphicNFAt_toMeromorphicNFAt
  by_cases hf : f ∈ (originalAnalyticPlace N τ).toValuationSubring
  · obtain ⟨g, hg, hvalue, he⟩ := original_regular_analytic_representative N τ f hf
    have he' := (hg.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hn).mp
      (he.trans hm.eq_nhdsNE_toMeromorphicNFAt)
    exact hvalue.symm.trans he'.eq_of_nhds
  · have ho : meromorphicOrderAt F (τ : ℂ) ≠ 0 := by
      intro he
      apply hf
      apply (originalAnalyticPlace_mem_iff N τ f).mpr
      change 0 ≤ meromorphicOrderAt F (τ : ℂ)
      rw [he]
    have ho' : meromorphicOrderAt (toMeromorphicNFAt F (τ : ℂ)) (τ : ℂ) ≠ 0 := by
      rwa [← meromorphicOrderAt_congr hm.eq_nhdsNE_toMeromorphicNFAt]
    have hz : toMeromorphicNFAt F (τ : ℂ) τ = 0 :=
      not_not.mp (hn.meromorphicOrderAt_eq_zero_iff.not.mp ho')
    change originalPlaceEval N ℂ (originalAnalyticPlace N τ) f = _
    rw [originalPlaceEval, dif_neg hf, hz]

private theorem eval_germ_normalForm (N : ℕ) [NeZero N]
    (f : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    (fun z : ℂ => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex z)) f) =ᶠ[𝓝 (τ : ℂ)]
      toMeromorphicNFAt (fun z : ℂ => realize N (f : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) := by
  let F : ℂ → ℂ := fun z => realize N (f : LaurentSeries ℂ) (ofComplex z)
  let U : Set ℂ := {z | 0 < z.im}
  have hm : MeromorphicOn F U := by
    intro z hz
    exact meromorphicAt_original_realize N f ⟨z, hz⟩
  have he : (fun z : ℂ => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex z)) f) =ᶠ[𝓝 (τ : ℂ)]
      toMeromorphicNFOn F U := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    have hz' : 0 < z.im := hz
    have h := eval_eq_normalForm N f (⟨z, hz'⟩ : ℍ)
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm hz']
    simpa only [ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_mk] using h
  exact he.trans (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hm τ.im_pos)

theorem meromorphicNFAt_originalPlaceEval (N : ℕ) [NeZero N]
    (f : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    MeromorphicNFAt
      (fun z : ℂ => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex z)) f) (τ : ℂ) := by
  rw [meromorphicNFAt_congr (eval_germ_normalForm N f τ)]
  exact meromorphicNFAt_toMeromorphicNFAt

theorem originalPlaceEval_analyticAt_iff (N : ℕ) [NeZero N]
    (f : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    AnalyticAt ℂ
      (fun z : ℂ => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex z)) f) (τ : ℂ) ↔
      f ∈ (originalAnalyticPlace N τ).toValuationSubring := by
  rw [← (meromorphicNFAt_originalPlaceEval N f τ).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_congr ((eval_germ_normalForm N f τ).filter_mono nhdsWithin_le_nhds),
    ← meromorphicOrderAt_congr (meromorphicAt_original_realize N f τ).eq_nhdsNE_toMeromorphicNFAt]
  exact (originalAnalyticPlace_mem_iff N τ f).symm

theorem originalPlaceEval_meromorphicOrderAt (N : ℕ) [NeZero N]
    (f : modularFunctionFieldOver N ℂ) (hf : f ≠ 0) (τ : ℍ) :
    meromorphicOrderAt
      (fun z : ℂ => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex z)) f) (τ : ℂ) =
      (((originalAnalyticRamification N τ : ℤ) * (originalAnalyticPlace N τ).ord f : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr ((eval_germ_normalForm N f τ).filter_mono nhdsWithin_le_nhds),
    ← meromorphicOrderAt_congr (meromorphicAt_original_realize N f τ).eq_nhdsNE_toMeromorphicNFAt]
  exact originalAnalyticPlace_order N τ f hf

end
end Dubon2026.SourceFunctionField

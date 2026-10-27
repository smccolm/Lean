import Dubon2026.SourceGammaOneAnalyticResidues

/-! DUB-17/18 -> original finite Gamma1 Hecke-character realization ->
Picard-period comparison. Adapt the proved original-field normal-form argument
to actual Gamma residue evaluation. Analyticity and order follow from the
original modular-ratio germs, with no supplied value comparison. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped Topology
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
  (hT : ModularGroup.T ∈ Γ)

private theorem eval_eq_normalForm
    (f : functionFieldOver Γ ℂ) (τ : ℍ) :
    placeEval hT (analyticPlace hT τ) f =
      toMeromorphicNFAt (fun z : ℂ => realize Γ (f : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) τ := by
  let F : ℂ → ℂ := fun z => realize Γ (f : LaurentSeries ℂ) (ofComplex z)
  have hm : MeromorphicAt F (τ : ℂ) := meromorphicAt_realize hT f τ
  have hn : MeromorphicNFAt (toMeromorphicNFAt F (τ : ℂ)) (τ : ℂ) :=
    meromorphicNFAt_toMeromorphicNFAt
  by_cases hf : f ∈ (analyticPlace hT τ).toValuationSubring
  · obtain ⟨g, hg, hvalue, he⟩ := regular_analytic_representative hT τ f hf
    have he' := (hg.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hn).mp
      (he.trans hm.eq_nhdsNE_toMeromorphicNFAt)
    exact hvalue.symm.trans he'.eq_of_nhds
  · have ho : meromorphicOrderAt F (τ : ℂ) ≠ 0 := by
      intro he
      apply hf
      apply (analyticPlace_mem_iff hT τ f).mpr
      change 0 ≤ meromorphicOrderAt F (τ : ℂ)
      rw [he]
    have ho' : meromorphicOrderAt (toMeromorphicNFAt F (τ : ℂ)) (τ : ℂ) ≠ 0 := by
      rwa [← meromorphicOrderAt_congr hm.eq_nhdsNE_toMeromorphicNFAt]
    have hz : toMeromorphicNFAt F (τ : ℂ) τ = 0 :=
      not_not.mp (hn.meromorphicOrderAt_eq_zero_iff.not.mp ho')
    change placeEval hT (analyticPlace hT τ) f = _
    rw [placeEval, SourceCurve.Place.rationalEval, dif_neg hf, hz]

private theorem eval_germ_normalForm
    (f : functionFieldOver Γ ℂ) (τ : ℍ) :
    (fun z : ℂ => placeEval hT (analyticPlace hT (ofComplex z)) f) =ᶠ[𝓝 (τ : ℂ)]
      toMeromorphicNFAt (fun z : ℂ => realize Γ (f : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) := by
  let F : ℂ → ℂ := fun z => realize Γ (f : LaurentSeries ℂ) (ofComplex z)
  let U : Set ℂ := {z | 0 < z.im}
  have hm : MeromorphicOn F U := by
    intro z hz
    exact meromorphicAt_realize hT f ⟨z, hz⟩
  have he : (fun z : ℂ => placeEval hT (analyticPlace hT (ofComplex z)) f) =ᶠ[𝓝 (τ : ℂ)]
      toMeromorphicNFOn F U := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    have hz' : 0 < z.im := hz
    have h := eval_eq_normalForm hT f (⟨z, hz'⟩ : ℍ)
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm hz']
    simpa only [ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_mk] using h
  exact he.trans (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hm τ.im_pos)

theorem meromorphicNFAt_placeEval
    (f : functionFieldOver Γ ℂ) (τ : ℍ) :
    MeromorphicNFAt
      (fun z : ℂ => placeEval hT (analyticPlace hT (ofComplex z)) f) (τ : ℂ) := by
  rw [meromorphicNFAt_congr (eval_germ_normalForm hT f τ)]
  exact meromorphicNFAt_toMeromorphicNFAt

theorem placeEval_analyticAt_iff
    (f : functionFieldOver Γ ℂ) (τ : ℍ) :
    AnalyticAt ℂ
      (fun z : ℂ => placeEval hT (analyticPlace hT (ofComplex z)) f) (τ : ℂ) ↔
      f ∈ (analyticPlace hT τ).toValuationSubring := by
  rw [← (meromorphicNFAt_placeEval hT f τ).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_congr ((eval_germ_normalForm hT f τ).filter_mono nhdsWithin_le_nhds),
    ← meromorphicOrderAt_congr (meromorphicAt_realize hT f τ).eq_nhdsNE_toMeromorphicNFAt]
  exact (analyticPlace_mem_iff hT τ f).symm

theorem placeEval_meromorphicOrderAt
    (f : functionFieldOver Γ ℂ) (hf : f ≠ 0) (τ : ℍ) :
    meromorphicOrderAt
      (fun z : ℂ => placeEval hT (analyticPlace hT (ofComplex z)) f) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) * (analyticPlace hT τ).ord f : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr ((eval_germ_normalForm hT f τ).filter_mono nhdsWithin_le_nhds),
    ← meromorphicOrderAt_congr (meromorphicAt_realize hT f τ).eq_nhdsNE_toMeromorphicNFAt]
  exact analyticPlace_order hT τ f hf

end
end Dubon2026.SourceFunctionField.GammaOne

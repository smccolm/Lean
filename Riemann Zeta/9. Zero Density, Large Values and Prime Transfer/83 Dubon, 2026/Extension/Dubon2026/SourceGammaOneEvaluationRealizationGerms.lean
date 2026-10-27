import Dubon2026.SourceGammaOneAnalyticEvaluation

/-! DUB-17/18 -> original finite Gamma1 Hecke-character realization ->
Picard-period differential pullback. Actual residue evaluation and the
original Gamma modular-ratio realization agree on punctured germs. The
proved regular residue limit supplies the comparison at nearby points. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped Topology
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
  (hT : ModularGroup.T ∈ Γ)

theorem placeEval_eq_realize_of_analyticAt
    (f : functionFieldOver Γ ℂ) (τ : ℍ)
    (ha : AnalyticAt ℂ (fun z : ℂ => realize Γ (f : LaurentSeries ℂ) (ofComplex z))
      (τ : ℂ)) :
    placeEval hT (analyticPlace hT τ) f =
      realize Γ (f : LaurentSeries ℂ) τ := by
  have hf : f ∈ (analyticPlace hT τ).toValuationSubring :=
    (analyticPlace_mem_iff hT τ f).mpr ha.meromorphicOrderAt_nonneg
  have h := tendsto_nhds_unique (realize_tendsto_residue hT τ f hf)
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [ofComplex_apply] using h

theorem placeEval_eventuallyEq_realize
    (f : functionFieldOver Γ ℂ) (τ : ℍ) :
    (fun z : ℂ => placeEval hT (analyticPlace hT (ofComplex z)) f) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => realize Γ (f : LaurentSeries ℂ) (ofComplex z) := by
  filter_upwards [(meromorphicAt_realize hT f τ).eventually_analyticAt,
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z ha hz
  have h := placeEval_eq_realize_of_analyticAt hT f ⟨z, hz⟩ ha
  simpa only [ofComplex_apply_of_im_pos hz] using h

end
end Dubon2026.SourceFunctionField.GammaOne

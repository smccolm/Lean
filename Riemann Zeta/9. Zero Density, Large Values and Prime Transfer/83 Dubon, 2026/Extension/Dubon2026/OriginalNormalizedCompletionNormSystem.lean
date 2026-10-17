import Dubon2026.OriginalNormalizedCompletionNormMap

/-! # One actual normalized global norm map compatible with all completions

The original finite class system constructs one global cocycle and its
fundamental acyclicity. Every normal decomposition group then has the
proved completion norm comparison for that same global cocycle. This
serves DUB-17's local inertia control; the inertia image is still separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))

/-- One source-normalized actual global cocycle with fundamental
acyclicity and the actual norm-map square at every normal decomposition
group and compatible closure. This proposition alone gives no witness. -/
def OriginalNormalizedClassCompletionNormSystem : Prop :=
  ∃ ψ : groupCohomology.cocycles₂ (originalIdeleClassRep K L),
    ∃ hD : ∀ T : Subgroup Gal(L/K),
      Limits.IsZero (groupCohomology (Rep.res T.subtype
        (originalFundamentalSplittingModule (originalIdeleClassRep K L) ψ)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res T.subtype
        (originalFundamentalSplittingModule (originalIdeleClassRep K L) ψ)) 2),
    addOrderOf (groupCohomology.H2π (originalIdeleClassRep K L) ψ) = Module.finrank K L ∧
    OriginalCompletionClassRestrictions K L (groupCohomology.H2π (originalIdeleClassRep K L) ψ) ∧
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
      [(OriginalFiniteDecompositionGroup K L w).Normal]
      (Ω : Type) [Field Ω]
      [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
      [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
      [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
      [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
      [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)],
      OriginalCompletionNormComparison K L w p hG ψ hD

/-- The actual finite normalized class system constructs the global
cocycle and all local norm comparisons, without any acyclicity or
local/global norm-map comparison premise. -/
theorem originalNormalizedClass_completion_norm_system
    (hsys : OriginalFiniteNormalizedClassSystem K L) :
    OriginalNormalizedClassCompletionNormSystem K L p hG := by
  obtain ⟨u, hu, h1, hc, hg, hl⟩ := hsys
  let C := originalIdeleClassRep K L
  obtain ⟨ψ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  obtain ⟨hD, _, _⟩ := originalFundamentalPGroup_positive_and_norm p hG C ψ h1 hc hg
  refine ⟨ψ, hD, hu, hl, ?_⟩
  intro v w _ _ Ω _ _ _ _ _ _ _ _
  exact originalCompletion_norm_comparison_of_normalization K L w p hG ψ hD v Ω hu hl

end
end Dubon2026

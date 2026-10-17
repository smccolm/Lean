import Dubon2026.OriginalCompletionClassMap

/-! # A compatible full-order cocycle on the actual completion units

The constructed finite local normalized class and the source's actual
completion restriction identify a cocycle with full decomposition order.
No local class, comparison certificate or local norm map is assumed.
This supplies DUB-17's local/global fundamental norm comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

include v Ω in
/-- The source-normalized global class constructs a compatible actual
completion cocycle of full decomposition-group order. -/
theorem originalCompletion_exists_compatible_full_order_cocycle
    (u : groupCohomology (originalIdeleClassRep K L) 2)
    (hu : addOrderOf u = Module.finrank K L)
    (hl : OriginalCompletionClassRestrictions K L u) :
    ∃ φ : groupCohomology.cocycles₂ (originalAdicUnitRep K L w),
      addOrderOf (groupCohomology.H2π (originalAdicUnitRep K L w) φ) =
        Nat.card (OriginalFiniteDecompositionGroup K L w) ∧
      groupCohomology.map (MonoidHom.id (OriginalFiniteDecompositionGroup K L w))
        (originalCompletionClassRepHom K L w) 2
        (groupCohomology.H2π (originalAdicUnitRep K L w) φ) =
      groupCohomology.map (OriginalFiniteDecompositionGroup K L w).subtype (𝟙 _) 2 u := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  obtain ⟨y, hy⟩ := originalFiniteLocal_exists_normalized_class
    (v.adicCompletion K) (w.adicCompletion L) Ω
  let z := originalFiniteCompletionLocalClass K L v w y
  have hz : (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
      (originalCompletionClassRepHom K L w) z =
      groupCohomology.map (OriginalFiniteDecompositionGroup K L w).subtype (𝟙 _) 2 u := by
    rw [originalCompletionClassRepHom, Functor.map_comp]
    exact (hl v w Ω y hy).symm
  obtain ⟨φ, hφ⟩ := (ModuleCat.epi_iff_surjective
    (groupCohomology.H2π (originalAdicUnitRep K L w))).mp inferInstance z
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ]
    exact originalCompletionClass_full_order K L v w u hu z hz
  · rw [hφ]
    exact hz

end
end Dubon2026

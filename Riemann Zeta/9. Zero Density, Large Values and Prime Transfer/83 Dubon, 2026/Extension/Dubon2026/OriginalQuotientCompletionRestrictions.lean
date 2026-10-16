import Dubon2026.OriginalCompletionClassRestrictions
import Dubon2026.OriginalClassesModOutsideH2Comparison

/-! # Source-normalized restrictions after the actual outside-unit quotient

The quotient is the literal original coefficient map. Its cohomology map
commutes with every original subgroup restriction, so the same normalized
completion classes give the required local images for DUB-17's quotient
class-system input to reverse localization.
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
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
/-- The actual original quotient cohomology map commutes with every subgroup restriction. -/
theorem originalClassQuotient_restriction_map (H : Subgroup Gal(L/K)) (n : ℕ) :
    (groupCohomology.functor ℤ Gal(L/K) n).map
        (originalIdeleClassesModOutsideRepHom K L S hS) ≫
      groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (originalIdeleClassesModOutsideRep K L S hS))) n =
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (originalIdeleClassRep K L))) n ≫
      (groupCohomology.functor ℤ H n).map ((Rep.resFunctor H.subtype).map
        (originalIdeleClassesModOutsideRepHom K L S hS)) := by
  change groupCohomology.map (MonoidHom.id _) _ n ≫ groupCohomology.map H.subtype _ n =
    groupCohomology.map H.subtype _ n ≫ groupCohomology.map (MonoidHom.id H) _ n
  simp only [← groupCohomology.map_comp, Category.comp_id]
  rfl

/-- The fixed quotient class has the prescribed actual images of all normalized completion classes. This proposition alone asserts no existence. -/
def OriginalCompletionQuotientRestrictions
    (u : groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2) : Prop :=
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
      (Ω : Type) [Field Ω]
      [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
      [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
      [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
      [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
      [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)],
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
      ∀ y : GaloisUnitContinuousH2 (K := v.adicCompletion K) (Ω := w.adicCompletion L),
        localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
          (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
            (w.adicCompletion L) Ω y) =
          (↑((1 : ℚ) / Module.finrank (v.adicCompletion K) (w.adicCompletion L)) : AddCircle (1 : ℚ)) →
        (groupCohomology.map (OriginalFiniteDecompositionGroup K L w).subtype
          (𝟙 (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
            (originalIdeleClassesModOutsideRep K L S hS))) 2).hom u =
          (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
            ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
              (originalIdeleClassesModOutsideRepHom K L S hS))
            ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
              ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
                (originalFullClassRepHom K L))
              ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
                (originalIdeleSingleFiniteRepHom K L w) (originalFiniteCompletionLocalClass K L v w y)))

/-- Every source-normalized restriction of the original class remains the actual normalized local image after quotienting outside units. -/
theorem originalClassQuotient_completion_restrictions
    (u : groupCohomology (originalIdeleClassRep K L) 2)
    (h : OriginalCompletionClassRestrictions K L u) :
    OriginalCompletionQuotientRestrictions K L S hS
      ((groupCohomology.functor ℤ Gal(L/K) 2).map
        (originalIdeleClassesModOutsideRepHom K L S hS) u) := by
  intro v w hw Ω _ _ _ _ _ _ _ _
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  dsimp only
  intro y hy
  have hn := congrArg (fun f => ModuleCat.Hom.hom f u)
    (originalClassQuotient_restriction_map K L S hS (OriginalFiniteDecompositionGroup K L w) 2)
  exact hn.trans (congrArg (fun z =>
    (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
      ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
        (originalIdeleClassesModOutsideRepHom K L S hS)) z) (h v w Ω y hy))

end
end Dubon2026

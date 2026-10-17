import Dubon2026.RestrictedFreeHomCocycleVanishing
import Dubon2026.RationalArithmeticOpenSubgroupClassH1

/-! # Actual arithmetic free-cover class Hom cocycles are coboundaries

The original finite Galois restriction has an open kernel. Generator
evaluation produces actual continuous class cocycles on that kernel,
whose coboundaries are already proved. The reconstruction removes the
free-cover Hom H1 obstacle to DUB-17's relation presentation of class duality.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original union's displayed rational inclusion. -/
local instance freeClassHomUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite stage's displayed rational inclusion. -/
local instance freeClassHomStageAlgebra : Algebra ℚ P := P.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

/-- The literal restricted original free-cover Hom into full arithmetic classes. -/
abbrev arithmeticRelationFreeClassHom :=
  (Rep.ihom (Rep.res (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ))
      (Rep.free ℤ Gal(P/ℚ) B))).obj (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticRelationFreeClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticRelationFreeClassHom Ω a ha P B)]

/-- The original discrete Hom coefficient has continuous integer scalar action. -/
local instance freeClassHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticRelationFreeClassHom Ω a ha P B)
      (arithmeticRelationFreeClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticRelationFreeClassHom Ω a ha P B)
    (arithmeticRelationFreeClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The original discrete class coefficient has continuous integer scalar action. -/
local instance classHomTargetContinuousSMul :
    @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Every actual continuous free-cover class Hom cocycle is a coboundary;
the needed kernel H1 vanishing is derived from the original arithmetic classes. -/
theorem arithmeticRelationFreeClassHomCocycle_exists_coboundary
    (c : continuousRepresentationCocyclesOne (arithmeticRelationFreeClassHom Ω a ha P B)) :
    ∃ v : arithmeticRelationFreeClassHom Ω a ha P B,
      ∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g v - v = c.val g := by
  letI : IsGalois ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res π (Rep.free ℤ Gal(P/ℚ) B)
  let C := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  have hπ : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective _
  apply restrictedFreeHomCocycle_exists_coboundary π hπ C c.val
  intro b
  let H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) :=
    ⟨π.ker, (isOpen_discrete ({1} : Set Gal(P/ℚ))).preimage
      (InfiniteGalois.restrictNormalHom_continuous P.toIntermediateField)⟩
  let e : A := Finsupp.single b (Finsupp.single 1 1)
  let f : H → C := fun t => DFunLike.coe (F := A →ₗ[ℤ] C) (c.val t.val) e
  have hf : f ∈ groupCohomology.cocycles₁ (Rep.res H.toSubgroup.subtype C) := by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g t
    have hc := congrArg (fun l : arithmeticRelationFreeClassHom Ω a ha P B =>
      DFunLike.coe (F := A →ₗ[ℤ] C) l e)
      ((groupCohomology.mem_cocycles₁_iff _).mp c.val.property g.val t.val)
    change DFunLike.coe (F := A →ₗ[ℤ] C) (c.val (g.val * t.val)) e =
      C.ρ g.val (DFunLike.coe (F := A →ₗ[ℤ] C) (c.val t.val)
        (Representation.free ℤ Gal(P/ℚ) B (π g.val⁻¹) e)) +
      DFunLike.coe (F := A →ₗ[ℤ] C) (c.val g.val) e at hc
    have hg : π g.val = 1 := g.property
    simpa only [f, e, Representation.free_single_single, map_inv, hg, inv_one, one_mul]
      using hc
  have hfcont : Continuous f :=
    (continuous_of_discreteTopology : Continuous (fun l : arithmeticRelationFreeClassHom Ω a ha P B =>
      DFunLike.coe (F := A →ₗ[ℤ] C) l e)).comp (c.property.comp continuous_subtype_val)
  let d : continuousRepresentationCocyclesOne (Rep.res H.toSubgroup.subtype C) :=
    ⟨⟨f, hf⟩, hfcont⟩
  obtain ⟨v, hv⟩ := rationalArithmeticOpenSubgroupClassOneCocycle_exists_coboundary Ω a ha H d
  refine ⟨v, ?_⟩
  intro t ht
  exact (hv ⟨t, ht⟩).symm

end
end Dubon2026

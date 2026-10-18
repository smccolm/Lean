import Dubon2026.PartialRestrictionFreeHomCocycle
import Dubon2026.ContinuousInfiniteGaloisUnitH1
import Dubon2026.GaloisUnitBaseChangeContinuity

/-! The local free-cover lifting input with its possibly proper decomposition-group image for DUB-17's finite relation route.
Generator evaluations on the actual specified restriction kernel are
continuous Galois unit cocycles. Native continuous Hilbert 90 and the
proved restricted-free reconstruction produce their original Hom lift. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω]
  (H : Type) [Group H] (ι : Gal(L/K) →* H) (α : Type)

/-- The actual global free cover restricted through the finite local decomposition group. -/
abbrev galoisTowerPartialFreeUnitHom :=
  (Rep.ihom (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K)))
    (Rep.free ℤ H α))).obj (Rep.ofAlgebraAutOnUnits K Ω)

variable [TopologicalSpace (galoisTowerPartialFreeUnitHom K L Ω H ι α)]
  [DiscreteTopology (galoisTowerPartialFreeUnitHom K L Ω H ι α)]

/-- Integer scalars act continuously on the original discrete free-cover Hom. -/
local instance galoisTowerPartialFreeUnitHomContinuousSMul :
    @ContinuousSMul ℤ (galoisTowerPartialFreeUnitHom K L Ω H ι α)
      (galoisTowerPartialFreeUnitHom K L Ω H ι α).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (galoisTowerPartialFreeUnitHom K L Ω H ι α)
    (galoisTowerPartialFreeUnitHom K L Ω H ι α).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Every original continuous free-cover Hom cocycle has a unit-valued
coboundary lift. The needed kernel vanishing comes from actual Hilbert 90,
not a supplied local cohomology or relation-lifting hypothesis. -/
theorem galoisTowerPartialFreeUnitHomCocycle_exists_coboundary
    (hι : Function.Injective ι)
    (c : continuousRepresentationCocyclesOne (galoisTowerPartialFreeUnitHom K L Ω H ι α)) :
    ∃ v : galoisTowerPartialFreeUnitHom K L Ω H ι α,
      ∀ g, (galoisTowerPartialFreeUnitHom K L Ω H ι α).ρ g v - v = c.val g := by
  let π : Gal(Ω/K) →* H := ι.comp (AlgEquiv.restrictNormalHom L)
  let A := Rep.res π (Rep.free ℤ H α)
  let C := Rep.ofAlgebraAutOnUnits K Ω
  apply partialRestrictionFreeHomCocycle_exists_coboundary π C c.val
  intro b h
  letI : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits L Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits L Ω) := ⟨rfl⟩
  let e : A := Finsupp.single b (Finsupp.single h 1)
  have hfix (g : Gal(Ω/L)) : π (g.restrictScalars K) = 1 := by
    have he : AlgEquiv.restrictNormalHom L (g.restrictScalars K) = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap L Ω).injective
      exact (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L x).trans (g.commutes x)
    change ι (AlgEquiv.restrictNormalHom L (g.restrictScalars K)) = 1
    rw [he, map_one]
  let f : Gal(Ω/L) → Rep.ofAlgebraAutOnUnits L Ω := fun g =>
    DFunLike.coe (F := A →ₗ[ℤ] C) (c.val (g.restrictScalars K)) e
  have hf : f ∈ groupCohomology.cocycles₁ (Rep.ofAlgebraAutOnUnits L Ω) := by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g t
    have hc := congrArg (fun l : galoisTowerPartialFreeUnitHom K L Ω H ι α =>
      DFunLike.coe (F := A →ₗ[ℤ] C) l e)
      ((groupCohomology.mem_cocycles₁_iff _).mp c.val.property
        (g.restrictScalars K) (t.restrictScalars K))
    change DFunLike.coe (F := A →ₗ[ℤ] C)
      (c.val (g.restrictScalars K * t.restrictScalars K)) e =
      C.ρ (g.restrictScalars K) (DFunLike.coe (F := A →ₗ[ℤ] C) (c.val (t.restrictScalars K))
        (Representation.free ℤ H α (π (g.restrictScalars K)⁻¹) e)) +
        DFunLike.coe (F := A →ₗ[ℤ] C) (c.val (g.restrictScalars K)) e at hc
    simpa only [f, e, Representation.free_single_single, map_inv, hfix, inv_one, one_mul]
      using hc
  have hr : Continuous (fun g : Gal(Ω/L) => g.restrictScalars K) := by
    apply (galoisBaseChangeRestriction_continuous K L Ω Ω).congr
    intro g
    apply AlgEquiv.ext
    intro x
    exact galoisBaseChangeRestriction_commutes K L Ω Ω g x
  have hfcont : Continuous f :=
    (continuous_of_discreteTopology : Continuous (fun l : galoisTowerPartialFreeUnitHom K L Ω H ι α =>
      (show Rep.ofAlgebraAutOnUnits L Ω from DFunLike.coe (F := A →ₗ[ℤ] C) l e))).comp
        (c.property.comp hr)
  let d : continuousRepresentationCocyclesOne (Rep.ofAlgebraAutOnUnits L Ω) := ⟨⟨f, hf⟩, hfcont⟩
  obtain ⟨β, hβ⟩ := continuousInfiniteGaloisUnitCocycle_exists_unit d
  refine ⟨Rep.toAdditive.symm (Additive.ofMul β), ?_⟩
  intro t ht
  have ht' : AlgEquiv.restrictNormalHom L t = 1 :=
    hι (ht.trans (map_one ι).symm)
  let s : Gal(Ω/L) := {
    __ := t.toRingEquiv
    commutes' := by
      intro x
      have hx := AlgEquiv.restrictNormal_commutes t L x
      change algebraMap L Ω (AlgEquiv.restrictNormalHom L t x) = t (algebraMap L Ω x) at hx
      rw [ht'] at hx
      exact hx.symm }
  exact (hβ s).symm

end
end Dubon2026

import Dubon2026.GaloisTowerPartialFreeUnitHom
import Dubon2026.GaloisTowerUnitHomDescent
import Dubon2026.OriginalRelationHomFromCoboundary
import Dubon2026.ContinuousEquivariantCoefficientMap

/-! Actual finite local unit relation representatives. Continuous Hilbert 90
constructs the lift on the original global free cover restricted through
the local decomposition group. Restriction to its relation kernel and
infinite fixed-field descent produce the finite local unit morphism, with
the original coboundary identity retained for the cup comparison. This is
the local construction needed by DUB-17's reverse H1 localization. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω] (H : Type) [Group H]
  (ι : Gal(L/K) →* H) (B : Rep.{0} ℤ H)

/-- The original coefficient Hom into local algebraic-closure units. -/
abbrev galoisTowerLocalCoefficientUnitHom :=
  (Rep.ihom (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)).obj
    (Rep.ofAlgebraAutOnUnits K Ω)

variable [TopologicalSpace (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)]
  [DiscreteTopology (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)]

/-- Integer multiplication is continuous on the original discrete local Hom. -/
local instance galoisTowerLocalCoefficientUnitHomContinuousSMul :
    @ContinuousSMul ℤ (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)
      (galoisTowerLocalCoefficientUnitHom K L Ω H ι B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)
    (galoisTowerLocalCoefficientUnitHom K L Ω H ι B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- An original local Hom cocycle gives a finite unit relation morphism and
the exact free-cover lift defining it. Proper decomposition-group images
are allowed; neither Hilbert 90 nor finite-value descent is a premise. -/
theorem galoisTowerLocalUnitCocycle_exists_relation_representative
    (hι : Function.Injective ι)
    (c : continuousRepresentationCocyclesOne (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)) :
    let π : Gal(Ω/K) →* H := ι.comp (AlgEquiv.restrictNormalHom L)
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let C := Rep.ofAlgebraAutOnUnits K Ω
    ∃ v : galoisTowerPartialFreeUnitHom K L Ω H ι B,
      ∃ ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L,
        ((Rep.resFunctor (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))).map ψ ≫
          finiteGaloisUnitTowerInclusion K L Ω).hom.toLinearMap =
            (show X.X₂ →ₗ[ℤ] C from v).comp X.f.hom.toLinearMap ∧
        ∀ g, (galoisTowerPartialFreeUnitHom K L Ω H ι B).ρ g v - v =
          (originalInternalHomPrecomposition C X.g).hom (c.val g) := by
  let π : Gal(Ω/K) →* H := ι.comp (AlgEquiv.restrictNormalHom L)
  let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
  let C := Rep.ofAlgebraAutOnUnits K Ω
  let U := galoisTowerPartialFreeUnitHom K L Ω H ι B
  letI : TopologicalSpace U := ⊥
  letI : DiscreteTopology U := ⟨rfl⟩
  letI : @ContinuousSMul ℤ U U.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ U U.hV2.toSMul _ _ continuous_of_discreteTopology
  let f := originalInternalHomPrecomposition C X.g
  let d := continuousCoefficientCocycleOneMap
    (galoisTowerLocalCoefficientUnitHom K L Ω H ι B) U f.hom.toLinearMap
      continuous_of_discreteTopology (Rep.hom_comm_apply f) c
  obtain ⟨v, hv⟩ := galoisTowerPartialFreeUnitHomCocycle_exists_coboundary
    K L Ω H ι B hι d
  obtain ⟨φ, hφ⟩ := originalRelationHom_exists_of_free_coboundary X C
    (fun g => c.val g) v hv
  obtain ⟨ψ, hψ⟩ := galoisTowerUnitHom_exists_descent K L Ω
    (Rep.res ι (originalRelationModule B)) φ
  refine ⟨v, ψ, ?_, hv⟩
  rw [hψ]
  exact hφ

end
end Dubon2026

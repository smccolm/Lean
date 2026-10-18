import Dubon2026.GaloisTowerLocalUnitRelation
import Dubon2026.OriginalInternalHomActionContinuity

/-! Continuity for the actual finite local relation presentation. This
supplies the action hypotheses of the existing continuous connecting/cup
identity, so DUB-17's local relation representative retains its original
continuous cohomology class. No discrete topology replaces the infinite
Galois group's Krull topology. -/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2
variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω]

/-- Restriction to the specified original Galois field is Krull-continuous. -/
theorem galoisTowerNormalRestriction_continuous :
    Continuous (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K)) := by
  exact (galoisBaseChangeRestriction_continuous K K L Ω).congr (fun _ => rfl)

variable [FiniteDimensional K L] (H : Type) [Group H] (ι : Gal(L/K) →* H)

/-- The actual coefficient restricted through the finite local group has
continuous action for the original infinite Galois topology. -/
theorem galoisTowerRestrictedCoefficientAction_continuous (A : Rep.{0} ℤ H)
    [TopologicalSpace (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) A)]
    [DiscreteTopology (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) A)] :
    let C := Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) A
    Continuous (fun z : Gal(Ω/K) × C => C.ρ z.1 z.2) := by
  let C := Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) A
  have h : Continuous (fun z : Gal(L/K) × C => A.ρ (ι z.1) z.2) := continuous_of_discreteTopology
  exact h.comp (((galoisTowerNormalRestriction_continuous K L Ω).comp continuous_fst).prodMk continuous_snd)

/-- The actual local Hom coefficient has continuous action, with finite
source and original unit-action continuity derived. -/
theorem galoisTowerLocalCoefficientUnitHomAction_continuous (B : Rep.{0} ℤ H) [Finite B]
    [TopologicalSpace (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)]
    [DiscreteTopology (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)] :
    Continuous (fun z : Gal(Ω/K) × galoisTowerLocalCoefficientUnitHom K L Ω H ι B =>
      (galoisTowerLocalCoefficientUnitHom K L Ω H ι B).ρ z.1 z.2) := by
  let A := Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B
  let C := Rep.ofAlgebraAutOnUnits K Ω
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  exact originalInternalHomAction_continuous_of_finite A C
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))

/-- The restricted original global free-cover Hom has continuous action;
its finite generation follows from the actual finite group and coefficient. -/
theorem galoisTowerPartialFreeUnitHomAction_continuous [Finite H] (α : Type) [Finite α]
    [TopologicalSpace (galoisTowerPartialFreeUnitHom K L Ω H ι α)]
    [DiscreteTopology (galoisTowerPartialFreeUnitHom K L Ω H ι α)] :
    Continuous (fun z : Gal(Ω/K) × galoisTowerPartialFreeUnitHom K L Ω H ι α =>
      (galoisTowerPartialFreeUnitHom K L Ω H ι α).ρ z.1 z.2) := by
  let A := Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (Rep.free ℤ H α)
  let C := Rep.ofAlgebraAutOnUnits K Ω
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : Module.Finite ℤ A := by
    change Module.Finite ℤ (α →₀ H →₀ ℤ)
    infer_instance
  exact originalInternalHomAction_continuous_of_finiteGenerated A C
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (Rep.free ℤ H α))
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))

end
end Dubon2026

import Dubon2026.ContinuousAlgebraicH1Injection
import Dubon2026.GaloisTowerLocalRelationFiniteComparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Identify the actual inflated finite H1 class by its literal algebraic
restriction. Degree-one injectivity removes dependence on the chosen
finite continuous lift in DUB-17's local cup-total construction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Algebraic H1 restriction through two literal group maps is their
composite restriction on the same coefficient cocycle. -/
theorem algebraicH1Restriction_comp {G J I : Type} [Group G] [Group J] [Group I]
    (A : Rep.{0} ℤ G) (α : J →* G) (β : I →* J) (y : groupCohomology A 1) :
    groupCohomology.map β (𝟙 (Rep.res (α.comp β) A)) 1
      (groupCohomology.map α (𝟙 (Rep.res α A)) 1 y) =
      groupCohomology.map (α.comp β) (𝟙 (Rep.res (α.comp β) A)) 1 y := by
  induction y using groupCohomology.H1_induction_on with
  | h c =>
    simp only [groupCohomology.H1π_comp_map_apply]
    rfl

attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] finiteLocalRelationCoefficientTopology finiteLocalRelationCoefficientDiscrete
  finiteLocalRelationCoefficientContinuousSMul localRelationCupCoefficientTopology
  localRelationCupCoefficientDiscrete localRelationCupCoefficientContinuousSMul
attribute [local instance 1100] finiteLocalRelationCoefficientTopology finiteLocalRelationCoefficientDiscrete
  finiteLocalRelationCoefficientContinuousSMul
variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω] [FiniteDimensional K L]
  (H : Type) [Group H] (ι : Gal(L/K) →* H) (B : Rep.{0} ℤ H)

/-- Actual finite local H1 inflation preserves the literal algebraic
restriction of every original coefficient cocycle. -/
theorem galoisTowerFiniteLocalH1Inflation_toAlgebraic
    (x : galoisTowerFiniteLocalCoefficientH1 K L H ι B) :
    continuousH1ToAlgebraic (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L)) B)
      (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
      (galoisTowerFiniteLocalH1Inflation K L Ω H ι B x) =
    groupCohomology.map (AlgEquiv.restrictNormalHom L)
      (𝟙 (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)) 1
      (continuousH1ToAlgebraic (Rep.res ι B) continuous_of_discreteTopology x) := by
  induction x using Quotient.inductionOn' with
  | h c =>
    exact (groupCohomology.H1π_comp_map_apply (AlgEquiv.restrictNormalHom L)
      (𝟙 (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)) c.val).symm

/-- Restricting the same global H1 class through the finite completion
and then its closure gives its original composite restriction. -/
theorem galoisTowerFiniteLocalH1Inflation_restriction
    (y : groupCohomology B 1)
    (x : galoisTowerFiniteLocalCoefficientH1 K L H ι B)
    (hx : continuousH1ToAlgebraic (Rep.res ι B) continuous_of_discreteTopology x =
      groupCohomology.map ι (𝟙 (Rep.res ι B)) 1 y) :
    continuousH1ToAlgebraic (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L)) B)
      (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
      (galoisTowerFiniteLocalH1Inflation K L Ω H ι B x) =
    groupCohomology.map (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K)))
      (𝟙 (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)) 1 y := by
  rw [galoisTowerFiniteLocalH1Inflation_toAlgebraic, hx]
  exact algebraicH1Restriction_comp B ι (AlgEquiv.restrictNormalHom L) y

/-- The continuous local class of the original global restriction is the
inflation of every finite continuous lift returned by the construction. -/
theorem galoisTowerFiniteLocalH1Inflation_eq_restriction
    (y : groupCohomology B 1)
    (x : galoisTowerFiniteLocalCoefficientH1 K L H ι B)
    (hx : continuousH1ToAlgebraic (Rep.res ι B) continuous_of_discreteTopology x =
      groupCohomology.map ι (𝟙 (Rep.res ι B)) 1 y)
    (z : galoisTowerLocalCoefficientH1 K L Ω H ι B)
    (hz : continuousH1ToAlgebraic (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L)) B)
      (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B) z =
      groupCohomology.map (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K)))
        (𝟙 (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)) 1 y) :
    galoisTowerFiniteLocalH1Inflation K L Ω H ι B x = z := by
  apply continuousH1ToAlgebraic_injective
    (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
  exact (galoisTowerFiniteLocalH1Inflation_restriction K L Ω H ι B y x hx).trans hz.symm

end
end Dubon2026

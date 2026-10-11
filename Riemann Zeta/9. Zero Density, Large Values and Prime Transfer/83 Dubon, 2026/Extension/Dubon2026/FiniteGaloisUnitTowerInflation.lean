import Dubon2026.GaloisUnitFiniteStageInflation

/-! # Actual unit-cohomology inflation between original finite Galois fields -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]

/-- The actual field-unit inclusion intertwines the original restricted
Galois action with the original action on the upper field. -/
def finiteGaloisUnitTowerInclusion :
    restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K L)
      (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)) ⟶
      Rep.ofAlgebraAutOnUnits K M :=
  Rep.ofHom {
    toLinearMap := (Units.map (algebraMap L M).toMonoidHom).toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      change Units.map (algebraMap L M).toMonoidHom
          (AlgEquiv.restrictNormalHom L g • (Additive.toMul (Rep.toAdditive x) : Lˣ)) =
        g • Units.map (algebraMap L M).toMonoidHom
          (Additive.toMul (Rep.toAdditive x) : Lˣ)
      apply Units.ext
      exact AlgEquiv.restrictNormal_commutes g L
        (Additive.toMul (Rep.toAdditive x) : Lˣ).val }

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

/-- Actual restriction precomposition and actual coefficient inclusion
on the original continuous two-cocycle modules. -/
def finiteGaloisUnitTowerCocycleInflation :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L) →ₗ[ℤ]
      continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K M) :=
  (continuousCoefficientCocycleTwoMap
    (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K L)
      (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)))
    (Rep.ofAlgebraAutOnUnits K M) (finiteGaloisUnitTowerInclusion K L M).hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply (finiteGaloisUnitTowerInclusion K L M))).comp
      (continuousRepresentationCocycleTwoRestriction (Rep.ofAlgebraAutOnUnits K L)
        (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)) continuous_of_discreteTopology)

/-- Actual finite-tower inflation on the existing original continuous H2 quotients. -/
def finiteGaloisUnitTowerH2Inflation :
    GaloisUnitContinuousH2 (K := K) (Ω := L) →ₗ[ℤ]
      GaloisUnitContinuousH2 (K := K) (Ω := M) := by
  let j : Gal(M/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  have hj : Continuous j := continuous_of_discreteTopology
  let φ := (finiteGaloisUnitTowerInclusion K L M).hom.toLinearMap
  let hL := discreteGaloisUnitAction_continuous (K := K) (Ω := L)
  let hM := discreteGaloisUnitAction_continuous (K := K) (Ω := M)
  exact (continuousCoefficientH2Map
    (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K L) j)
    (Rep.ofAlgebraAutOnUnits K M) φ continuous_of_discreteTopology
    (Rep.hom_comm_apply (finiteGaloisUnitTowerInclusion K L M))
    (restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits K L) j hj hL) hM).comp
      (continuousRepresentationH2Restriction (Rep.ofAlgebraAutOnUnits K L) hL j hj)

/-- The H2 map retains the exact original inflated representative. -/
theorem finiteGaloisUnitTowerH2Inflation_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    finiteGaloisUnitTowerH2Inflation K L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteGaloisUnitTowerCocycleInflation K L M c) := by
  rfl

omit [IsGalois K M] in
/-- The original inflated value is the actual unit inclusion at the two
original restricted automorphisms. -/
theorem finiteGaloisUnitTowerCocycleInflation_apply
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L))
    (g h : Gal(M/K)) :
    Additive.toMul (Rep.toAdditive ((finiteGaloisUnitTowerCocycleInflation K L M c).val (g, h))) =
      Units.map (algebraMap L M).toMonoidHom
        (Additive.toMul (Rep.toAdditive
          (c.val (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L h)))) := by
  rfl

end
end Dubon2026

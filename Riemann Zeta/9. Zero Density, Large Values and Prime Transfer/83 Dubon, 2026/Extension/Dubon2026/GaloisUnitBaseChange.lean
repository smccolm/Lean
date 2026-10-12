import Dubon2026.FiniteGaloisUnitTowerInflation

/-! # Original unit-cohomology maps for genuine changes of base field -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]

/-- Change the fixed base from E to K and then restrict the same original
automorphism to L. This is the genuine homomorphism between the field groups. -/
def galoisBaseChangeRestriction : Gal(M/E) →* Gal(L/K) where
  toFun g := AlgEquiv.restrictNormalHom L (g.restrictScalars K)
  map_one' := by
    change AlgEquiv.restrictNormalHom L (1 : Gal(M/K)) = 1
    exact map_one _
  map_mul' g h := by
    change AlgEquiv.restrictNormalHom L (g.restrictScalars K * h.restrictScalars K) = _
    exact map_mul _ _ _

/-- Restriction commutes with the literal inclusion of the original L value into M. -/
theorem galoisBaseChangeRestriction_commutes (g : Gal(M/E)) (x : L) :
    algebraMap L M (galoisBaseChangeRestriction K E L M g x) = g (algebraMap L M x) := by
  exact AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L x

/-- The original L-unit inclusion intertwines the original actions after
the actual change of base. -/
def galoisUnitBaseChangeInclusion :
    restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K L)
      (galoisBaseChangeRestriction K E L M) ⟶ Rep.ofAlgebraAutOnUnits E M :=
  Rep.ofHom {
    toLinearMap := (Units.map (algebraMap L M).toMonoidHom).toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      change Units.map (algebraMap L M).toMonoidHom
        (galoisBaseChangeRestriction K E L M g • (Additive.toMul (Rep.toAdditive x) : Lˣ)) =
          g • Units.map (algebraMap L M).toMonoidHom
            (Additive.toMul (Rep.toAdditive x) : Lˣ)
      apply Units.ext
      exact galoisBaseChangeRestriction_commutes K E L M g _ }

variable [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

/-- Literal group precomposition and coefficient inclusion define actual
base change on the original continuous cocycles. -/
def finiteGaloisUnitBaseChangeCocycle :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L) →ₗ[ℤ]
      continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits E M) :=
  (continuousCoefficientCocycleTwoMap
    (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K L)
      (galoisBaseChangeRestriction K E L M))
    (Rep.ofAlgebraAutOnUnits E M) (galoisUnitBaseChangeInclusion K E L M).hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply (galoisUnitBaseChangeInclusion K E L M))).comp
      (continuousRepresentationCocycleTwoRestriction (Rep.ofAlgebraAutOnUnits K L)
        (galoisBaseChangeRestriction K E L M) continuous_of_discreteTopology)

/-- The same original maps descend through actual continuous coboundaries
to base change on original continuous Galois-unit H2. -/
def finiteGaloisUnitBaseChangeH2 :
    GaloisUnitContinuousH2 (K := K) (Ω := L) →ₗ[ℤ]
      GaloisUnitContinuousH2 (K := E) (Ω := M) := by
  let j := galoisBaseChangeRestriction K E L M
  have hj : Continuous j := continuous_of_discreteTopology
  let φ := (galoisUnitBaseChangeInclusion K E L M).hom.toLinearMap
  let hL := discreteGaloisUnitAction_continuous (K := K) (Ω := L)
  let hM := discreteGaloisUnitAction_continuous (K := E) (Ω := M)
  exact (continuousCoefficientH2Map
    (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K L) j)
    (Rep.ofAlgebraAutOnUnits E M) φ continuous_of_discreteTopology
    (Rep.hom_comm_apply (galoisUnitBaseChangeInclusion K E L M))
    (restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits K L) j hj hL) hM).comp
      (continuousRepresentationH2Restriction (Rep.ofAlgebraAutOnUnits K L) hL j hj)

/-- Base change retains the literal original cocycle representative. -/
theorem finiteGaloisUnitBaseChangeH2_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    finiteGaloisUnitBaseChangeH2 K E L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteGaloisUnitBaseChangeCocycle K E L M c) := by
  rfl

end
end Dubon2026

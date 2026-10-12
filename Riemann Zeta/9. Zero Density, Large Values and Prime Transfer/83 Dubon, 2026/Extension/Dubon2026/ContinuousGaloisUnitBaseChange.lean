import Dubon2026.GaloisUnitBaseChangeContinuity

/-! # Actual base change on original infinite continuous Galois unit H2 -/

namespace Dubon2026
noncomputable section

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]

variable [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

/-- Literal group precomposition and coefficient inclusion define actual
base change on the original continuous cocycles. -/
def continuousGaloisUnitBaseChangeCocycle :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L) →ₗ[ℤ]
      continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits E M) :=
  (continuousCoefficientCocycleTwoMap
    (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K L)
      (galoisBaseChangeRestriction K E L M))
    (Rep.ofAlgebraAutOnUnits E M) (galoisUnitBaseChangeInclusion K E L M).hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply (galoisUnitBaseChangeInclusion K E L M))).comp
      (continuousRepresentationCocycleTwoRestriction (Rep.ofAlgebraAutOnUnits K L)
        (galoisBaseChangeRestriction K E L M) (galoisBaseChangeRestriction_continuous K E L M))

/-- The same original maps descend through actual continuous coboundaries
to base change on original continuous Galois-unit H2. -/
def continuousGaloisUnitBaseChangeH2 :
    GaloisUnitContinuousH2 (K := K) (Ω := L) →ₗ[ℤ]
      GaloisUnitContinuousH2 (K := E) (Ω := M) := by
  let j := galoisBaseChangeRestriction K E L M
  have hj : Continuous j := galoisBaseChangeRestriction_continuous K E L M
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
theorem continuousGaloisUnitBaseChangeH2_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    continuousGaloisUnitBaseChangeH2 K E L M (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousGaloisUnitBaseChangeCocycle K E L M c) := by
  rfl

/-- For actual finite extensions the original infinite construction
agrees with the already proved finite base-change map on the same classes. -/
theorem continuousGaloisUnitBaseChangeH2_eq_finite [FiniteDimensional E M] :
    continuousGaloisUnitBaseChangeH2 K E L M = finiteGaloisUnitBaseChangeH2 K E L M := by
  rfl

end
end Dubon2026

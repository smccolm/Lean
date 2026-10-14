import Dubon2026.ArithmeticKummerCyclicH2Stage

/-! # Original arithmetic unit restriction is literal field base change

The algebra on the same original local closure comes from the exact
embedding already defining arithmetic restriction. Its field-element
commutation identifies the group maps, and the identical unit cocycles
identify continuous H2. This connects the constructed arithmetic cyclic
stage to the local completion pairing on DUB-17's invariant-sum route.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra
  AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] rationalPrimeLocalField_charZero
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)

/-- Retain the original rational scalar module on the original prime completion. -/
local instance arithmeticUnitBaseChangePrimeModule : Module ℚ (rationalPrimeLocalField p hp) :=
  Algebra.toModule

/-- Use the exact embedding that defines original arithmetic restriction. -/
local instance arithmeticUnitBaseChangeAlgebra :
    Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
  (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a).toAlgebra

/-- Use the scalar action of that exact original arithmetic embedding. -/
local instance arithmeticUnitBaseChangeSMul :
    SMul (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
  (arithmeticUnitBaseChangeAlgebra a p hp).toSMul

/-- The original arithmetic embedding preserves the original rational scalars. -/
local instance arithmeticUnitBaseChangeTower :
    IsScalarTower ℚ (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
  IsScalarTower.of_algHom
    (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a)

/-- The literal field base-change restriction is exactly the original arithmetic Galois restriction. -/
theorem rationalArithmeticUnitBaseChangeRestriction :
    galoisBaseChangeRestriction ℚ (rationalPrimeLocalField p hp)
      (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) =
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a).injective
  exact (galoisBaseChangeRestriction_commutes ℚ (rationalPrimeLocalField p hp)
    (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) g x).trans
    (rationalPrimeArithmeticRestriction_commutes a p hp g x).symm

variable [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The original arithmetic continuous unit-H2 restriction is the same-cocycle actual field base change through its original local embedding. -/
theorem rationalArithmeticUnitH2Restriction_eq_baseChange
    (x : ContinuousRepresentationH2 (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitAction_continuous a)) :
    rationalArithmeticUnitH2Restriction a p hp x =
      continuousGaloisUnitBaseChangeH2 ℚ (rationalPrimeLocalField p hp)
        (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change (Units.map (rationalArithmeticLocalEmbedding
      (K := rationalPrimeLocalClosure p hp) a).toMonoidHom).toAdditive
      (c.val (rationalPrimeArithmeticRestriction a p hp z.1,
        rationalPrimeArithmeticRestriction a p hp z.2)) =
      (Units.map (rationalArithmeticLocalEmbedding
        (K := rationalPrimeLocalClosure p hp) a).toMonoidHom).toAdditive
        (c.val (galoisBaseChangeRestriction ℚ (rationalPrimeLocalField p hp)
          (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) z.1,
          galoisBaseChangeRestriction ℚ (rationalPrimeLocalField p hp)
            (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) z.2))
    rw [rationalArithmeticUnitBaseChangeRestriction]
    rfl

end
end Dubon2026

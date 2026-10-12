import Dubon2026.ArithmeticUnitLocalMap
import Dubon2026.ArithmeticRootH2Restriction

/-! # The original arithmetic Kummer square on continuous H2

The actual field embedding and Galois restriction induce global-to-local
unit cohomology. The genuine Kummer square commutes on the same continuous
cocycle quotients. This connects DUB-17's coherent character pairings to
the original local invariant; global reciprocity is still to be proved.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticGlobalRootContinuousSMul

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)

/-- Retain the original rational algebra for the actual unit cohomology. -/
local instance arithmeticUnitH2Algebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'

variable [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

local instance arithmeticGlobalUnitContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitRepresentation a).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The original arithmetic unit action is continuous for its discrete
coefficients and the actual Krull topology, by existing Galois continuity. -/
theorem rationalArithmeticUnitAction_continuous :
    Continuous (fun z : rationalArithmeticGaloisGroup a ×
      rationalArithmeticUnitRepresentation a =>
        (rationalArithmeticUnitRepresentation a).ρ z.1 z.2) := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) :=
    inferInstanceAs (TopologicalSpace (rationalArithmeticUnitRepresentation a))
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) :=
    inferInstanceAs (DiscreteTopology (rationalArithmeticUnitRepresentation a))
  exact discreteGaloisUnitAction_continuous (K := ℚ) (Ω := rationalUnramifiedExtension a)

/-- Original unit cohomology restricts by the actual arithmetic Galois map
and the literal embedding of the original global coefficient units. -/
def rationalArithmeticUnitH2Restriction :
    ContinuousRepresentationH2 (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitAction_continuous a) →ₗ[ℤ]
    GaloisUnitContinuousH2 (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) :=
  let A := rationalArithmeticUnitRepresentation a
  let j := rationalPrimeArithmeticRestriction a p hp
  (continuousCoefficientH2Map (restrictedCoefficientRep A j.toMonoidHom) _
    (rationalArithmeticUnitLocalMap a p hp) continuous_of_discreteTopology
    (rationalArithmeticUnitLocalMap_equivariant a p hp)
    (restrictedCoefficientAction_continuous A j.toMonoidHom j.continuous
      (rationalArithmeticUnitAction_continuous a)) _).comp
        (continuousRepresentationH2Restriction A (rationalArithmeticUnitAction_continuous a)
          j.toMonoidHom j.continuous)

variable (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]

/-- The original arithmetic root inclusion induces its genuine Kummer H2
map on the original continuous cocycles and coboundaries. -/
def rationalArithmeticKummerH2Inclusion :
    ContinuousRepresentationH2 (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootAction_continuous a q) →ₗ[ℤ]
    ContinuousRepresentationH2 (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitAction_continuous a) :=
  continuousCoefficientH2Map _ _ (rationalArithmeticKummerInclusion a q)
    continuous_of_discreteTopology
    (Rep.hom_comm_apply (galoisKummerInclusion (K := ℚ) (Ω := rationalUnramifiedExtension a) q)) _ _

/-- The original global-to-local maps commute with the actual Kummer H2
inclusions. No reciprocity or sum-of-invariants premise is used. -/
theorem rationalArithmeticUnitH2Restriction_kummer
    (x : ContinuousRepresentationH2 (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootAction_continuous a q)) :
    rationalArithmeticUnitH2Restriction a p hp (rationalArithmeticKummerH2Inclusion a q x) =
      galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q
        (rationalArithmeticRootH2Restriction a q hqa p hp x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact rationalArithmeticUnitLocalMap_kummer a p hp q hqa
      (c.val (rationalPrimeArithmeticRestriction a p hp z.1,
        rationalPrimeArithmeticRestriction a p hp z.2))

end
end Dubon2026

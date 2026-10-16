import Dubon2026.ContinuousCoefficientMackey
import Dubon2026.ArithmeticUnitH2Restriction
import Dubon2026.ContinuousCorestrictionCoefficientMap

/-! # Actual prime restriction of the original arithmetic unit transfer

The original prime-completion restriction and actual unit embedding consume
the proved continuous Mackey formula. Individual orbit/completion field
identifications remain a separate DUB-17 arithmetic obligation.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators NumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (S : Subgroup (rationalArithmeticGaloisGroup a)) (hS : IsOpen (S : Set (rationalArithmeticGaloisGroup a)))
  [Fintype (rationalArithmeticGaloisGroup a ⧸ S)]
  [Fintype (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom S)]
  [∀ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom S,
    Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
      cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom S ω.out)]

/-- The original arithmetic unit module keeps its actual integer action
and the given discrete topology. -/
local instance arithmeticOrbitUnitContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitRepresentation a).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The actual arithmetic unit localization of a genuine corestriction
is the sum of genuine local stabilizer corestrictions after the actual
global-to-local unit embedding, with all cohomological identities proved. -/
theorem rationalArithmeticUnitH2_restriction_corestriction_orbits
    (c : continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep (rationalArithmeticUnitRepresentation a) S.subtype)) :
    let A := rationalArithmeticUnitRepresentation a
    let j := rationalPrimeArithmeticRestriction a p hp
    let B := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    let hB := discreteGaloisUnitAction_continuous
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp)
    rationalArithmeticUnitH2Restriction a p hp
        (continuousRepresentationH2Corestriction A (rationalArithmeticUnitAction_continuous a)
          S hS (Submodule.Quotient.mk c)) =
      ∑ ω : cosetOrbitIndex j.toMonoidHom S,
        continuousRepresentationH2Corestriction B hB
          (cosetOrbitStabilizer j.toMonoidHom S ω.out)
          (cosetOrbitStabilizer_isOpen j.toMonoidHom j.continuous S hS ω.out)
          (Submodule.Quotient.mk
            (continuousCoefficientCocycleTwoMap
              (restrictedCoefficientRep (restrictedCoefficientRep A j.toMonoidHom)
                (cosetOrbitStabilizer j.toMonoidHom S ω.out).subtype)
              (restrictedCoefficientRep B (cosetOrbitStabilizer j.toMonoidHom S ω.out).subtype)
              (rationalArithmeticUnitLocalMap a p hp) continuous_of_discreteTopology
              (fun g x => rationalArithmeticUnitLocalMap_equivariant a p hp g x)
              (continuousCosetOrbitCocycle A (rationalArithmeticUnitAction_continuous a)
                j.toMonoidHom j.continuous S ω.out c))) := by
  exact continuousCoefficientH2Map_restriction_corestriction_orbits
    (rationalArithmeticUnitRepresentation a) (rationalArithmeticUnitAction_continuous a)
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalPrimeArithmeticRestriction a p hp).continuous
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
    (discreteGaloisUnitAction_continuous
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp))
    (rationalArithmeticUnitLocalMap a p hp) continuous_of_discreteTopology
    (rationalArithmeticUnitLocalMap_equivariant a p hp) S hS c

end
end Dubon2026

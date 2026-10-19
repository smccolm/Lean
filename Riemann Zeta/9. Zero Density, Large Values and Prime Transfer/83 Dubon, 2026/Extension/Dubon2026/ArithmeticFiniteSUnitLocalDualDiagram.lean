import Dubon2026.OriginalDualRestrictedPostcomposition
import Dubon2026.ArithmeticSUnitLocalMorphism
import Dubon2026.GaloisUnitRelationDualSequence
import Dubon2026.ArithmeticRelationDualSequence
import Dubon2026.RationalArithmeticOriginalCompletionRestriction

/-! The actual arithmetic S-unit localization induces the local dual
relation diagram. Its local dual exactness is derived from unit roots,
providing the coefficient comparison for DUB-17's constructed global class. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ)) (p : ℕ) (hp : p.Prime)

/-- The actual local diagram is induced by the literal arithmetic
S-unit map on the original restricted finite relation presentation. -/
def arithmeticFiniteSUnitLocalDualDiagram :
    let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
    let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
    let E := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    (originalContravariantHomShortComplex X D).map (Rep.resFunctor j) ⟶
      originalContravariantHomShortComplex (X.map (Rep.resFunctor j)) E :=
  let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
  let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
  let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
  let E := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  originalDualRestrictedPostcomposition j D E X (rationalArithmeticSUnitLocalMorphism a ha p hp)

/-- The local target of the actual arithmetic dual diagram is short
exact, with all unit root and integer extension inputs derived. -/
theorem arithmeticFiniteSUnitLocalDualSequence_shortExact
    (q : ℕ) [Fact q.Prime] (hB : ∀ b : B, q • b = 0) :
    let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
    let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let E := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    (originalContravariantHomShortComplex (X.map (Rep.resFunctor j)) E).ShortExact := by
  intro π j X E
  exact galoisUnitRelationDualSequence_shortExact
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    Gal(F/ℚ) (π.comp j) q B hB

end
end Dubon2026

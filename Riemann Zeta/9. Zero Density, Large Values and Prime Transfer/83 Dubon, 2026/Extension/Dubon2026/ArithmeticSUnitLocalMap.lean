import Dubon2026.ArithmeticUnitLocalMap
import Dubon2026.ArithmeticSUnitKummerSequence

/-! The actual arithmetic S-unit coefficient map to original local units.
The native field-unit embedding and S-unit inclusion give equivariance and
the exact original root square. This is the coefficient map required by
DUB-17's constructed global dual class/local Cartier comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticUnitMapAlgebra

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime)

/-- The literal arithmetic S-unit inclusion followed by the original
global-to-local field-unit map. -/
def rationalArithmeticSUnitLocalMap :
    originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha →ₗ[ℤ]
      Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) :=
  (rationalArithmeticUnitLocalMap a p hp).comp
    (originalArithmeticSUnitInclusion ℚ (AlgebraicClosure ℚ) a ha).hom.toLinearMap

/-- The S-unit coefficient map intertwines the actual arithmetic
restriction with the original prime-local unit action. -/
theorem rationalArithmeticSUnitLocalMap_equivariant
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (x : originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha) :
    rationalArithmeticSUnitLocalMap a ha p hp
      ((originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha).ρ
        (rationalPrimeArithmeticRestriction a p hp g) x) =
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)).ρ g
        (rationalArithmeticSUnitLocalMap a ha p hp x) := by
  exact (congrArg (rationalArithmeticUnitLocalMap a p hp)
    (Rep.hom_comm_apply (originalArithmeticSUnitInclusion ℚ (AlgebraicClosure ℚ) a ha)
      (rationalPrimeArithmeticRestriction a p hp g) x)).trans
    (rationalArithmeticUnitLocalMap_equivariant a p hp g
      ((originalArithmeticSUnitInclusion ℚ (AlgebraicClosure ℚ) a ha).hom x))

/-- The same original arithmetic root has precisely its existing local
Kummer image after passing through the actual arithmetic S-units. -/
theorem rationalArithmeticSUnitLocalMap_kummer
    (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (x : rationalArithmeticRootRepresentation a q) :
    rationalArithmeticSUnitLocalMap a ha p hp
      ((originalArithmeticSUnitKummerInclusion ℚ (AlgebraicClosure ℚ) a ha q).hom x) =
      (galoisKummerInclusion (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q).hom.toLinearMap
        (rationalArithmeticRootLocalEquiv a q hqa p hp x) := by
  have h := LinearMap.congr_fun
    (originalArithmeticSUnitKummerInclusion_field_comparison ℚ (AlgebraicClosure ℚ) a ha q) x
  exact (congrArg (rationalArithmeticUnitLocalMap a p hp) h).trans
    (rationalArithmeticUnitLocalMap_kummer a p hp q hqa x)

end
end Dubon2026

import Dubon2026.ArithmeticRootLocalMap

/-! # Original arithmetic unit coefficients and the Kummer restriction square

The global and local unit maps use the same actual field embedding as the
arithmetic restriction. The Kummer square connects coherent root classes to
unit cohomology, where DUB-17's global reciprocity must be established.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)

/-- Preserve the rational algebra used by the original arithmetic embedding. -/
local instance arithmeticUnitMapAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'

/-- Use the actual arithmetic automorphism action on original field units. -/
local instance arithmeticUnitMapAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rationalUnramifiedExtension a)ˣ :=
  inferInstanceAs (MulDistribMulAction
    Gal(rationalUnramifiedExtension a / ℚ) (rationalUnramifiedExtension a)ˣ)

/-- The actual units in the original arithmetic extension, with their
integer-linear original Galois action. -/
def rationalArithmeticUnitRepresentation : Rep ℤ (rationalArithmeticGaloisGroup a) :=
  Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)

/-- The genuine global-to-local unit coefficient map induced by the exact
arithmetic field embedding used for restriction. -/
def rationalArithmeticUnitLocalMap :
    rationalArithmeticUnitRepresentation a →ₗ[ℤ]
      Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) :=
  (Units.map (rationalArithmeticLocalEmbedding
    (K := rationalPrimeLocalClosure p hp) a).toMonoidHom).toAdditive.toIntLinearMap

/-- The original unit coefficient inclusion intertwines precisely the
existing arithmetic Galois restriction with the actual local action. -/
theorem rationalArithmeticUnitLocalMap_equivariant
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (x : rationalArithmeticUnitRepresentation a) :
    rationalArithmeticUnitLocalMap a p hp
      ((rationalArithmeticUnitRepresentation a).ρ (rationalPrimeArithmeticRestriction a p hp g) x) =
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)).ρ g (rationalArithmeticUnitLocalMap a p hp x) := by
  apply Rep.toAdditive.injective
  apply Additive.toMul.injective
  apply Units.ext
  exact rationalPrimeArithmeticRestriction_commutes a p hp g _

variable (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The original Kummer coefficient inclusion in the genuine arithmetic
extension, with the same global root and unit representations. -/
def rationalArithmeticKummerInclusion :
    rationalArithmeticRootRepresentation a q →ₗ[ℤ] rationalArithmeticUnitRepresentation a :=
  (galoisKummerInclusion (K := ℚ) (Ω := rationalUnramifiedExtension a) q).hom.toLinearMap

/-- The actual arithmetic coefficient maps commute with the genuine
Kummer inclusions, by the proved field value of every mapped root. -/
theorem rationalArithmeticUnitLocalMap_kummer
    (x : rationalArithmeticRootRepresentation a q) :
    rationalArithmeticUnitLocalMap a p hp (rationalArithmeticKummerInclusion a q x) =
      (galoisKummerInclusion (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q).hom.toLinearMap
        (rationalArithmeticRootLocalEquiv a q hqa p hp x) := by
  apply Rep.toAdditive.injective
  apply Additive.toMul.injective
  apply Units.ext
  exact (rationalArithmeticRootLocalEquiv_value a q hqa p hp x).symm

end
end Dubon2026

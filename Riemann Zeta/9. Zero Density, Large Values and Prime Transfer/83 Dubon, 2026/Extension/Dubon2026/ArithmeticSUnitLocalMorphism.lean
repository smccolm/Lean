import Dubon2026.ArithmeticSUnitLocalMap
import Dubon2026.ContinuousRepresentationRestriction

/-! Bundle the actual arithmetic S-unit localization as a representation
morphism for the local connecting-map diagram required by DUB-17. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime)

/-- The original S-unit map, with its proved action compatibility, is
an actual morphism after arithmetic Galois restriction. -/
def rationalArithmeticSUnitLocalMorphism :
    Rep.res (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha) ⟶
      Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) :=
  Rep.ofHom ⟨rationalArithmeticSUnitLocalMap a ha p hp, fun g => by
    apply LinearMap.ext
    intro x
    exact rationalArithmeticSUnitLocalMap_equivariant a ha p hp g x⟩

end
end Dubon2026

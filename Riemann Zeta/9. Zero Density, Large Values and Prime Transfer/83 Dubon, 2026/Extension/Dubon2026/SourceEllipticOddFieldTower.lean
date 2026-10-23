import Dubon2026.SourceEllipticOddRationalEmbedding
import Mathlib.FieldTheory.Relrank

/-! The actual elliptic field degree over the explicit odd quotient x-coordinate.
The already proved quadratic elliptic extension and rational degree 2n+1 are
composed inside the original function field. This discharges the finite-degree
input preceding the quotient equation and point homomorphism (DUB-17/18). -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticFunctionField
open scoped IntermediateField

namespace Dubon2026.SourceEllipticVelu

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The elliptic function field is quadratic over the actual rational-coordinate image. -/
theorem finrank_rationalCoordinateRange :
    Module.finrank (rationalCoordinateHom W).fieldRange W.toAffine.FunctionField = 2 := by
  let e := rationalCoordinateHom W
  letI : Algebra (RatFunc F) W.toAffine.FunctionField := e.toRingHom.toAlgebra
  haveI : IsScalarTower F[X] (RatFunc F) W.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun p => by
      change algebraMap F[X] W.toAffine.FunctionField p = e (algebraMap F[X] (RatFunc F) p)
      rw [rationalCoordinateHom_polynomial, algebraMap_eq_aeval_genericX]
  have he : Module.finrank (RatFunc F) W.toAffine.FunctionField =
      Module.finrank e.fieldRange W.toAffine.FunctionField :=
    Algebra.finrank_eq_of_equiv_equiv (AlgEquiv.ofInjective e e.injective).toRingEquiv
      (RingEquiv.refl _) (by ext z; rfl)
  exact he.symm.trans (finrank_functionField W.toAffine (RatFunc F))

variable [DecidableEq F] {W} {Q : W.toAffine.Point} {n : ℕ}

/-- The odd rational degree is preserved in its actual embedded coordinate field. -/
theorem relfinrank_odd_generic_coordinate (hQ : addOrderOf Q = 2 * n + 1) :
    IntermediateField.relfinrank F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯
      (rationalCoordinateHom W).fieldRange = 2 * n + 1 := by
  have hm : F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯ =
      F⟮ratFuncVeluX W (oddOrderSummingSet W Q n)⟯.map (rationalCoordinateHom W) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, rationalCoordinateHom_ratFuncVeluX]
  rw [hm, ← IntermediateField.finrank_comap, IntermediateField.comap_map]
  exact finrank_odd_ratFuncVeluX hQ

/-- The complete elliptic field has degree twice the odd order over the actual quotient x-coordinate. -/
theorem finrank_odd_generic_coordinate (hQ : addOrderOf Q = 2 * n + 1) :
    Module.finrank F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯ W.toAffine.FunctionField =
      2 * (2 * n + 1) := by
  have hle : F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯ ≤
      (rationalCoordinateHom W).fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z (rfl : z = _)
    exact ⟨ratFuncVeluX W _, rationalCoordinateHom_ratFuncVeluX W _⟩
  rw [← IntermediateField.relfinrank_mul_finrank_top hle,
    relfinrank_odd_generic_coordinate hQ, finrank_rationalCoordinateRange]
  omega

/-- Finite dimensionality over the actual odd quotient coordinate has no additional premise. -/
theorem finiteDimensional_odd_generic_coordinate (hQ : addOrderOf Q = 2 * n + 1) :
    FiniteDimensional F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯ W.toAffine.FunctionField :=
  .of_finrank_pos (by rw [finrank_odd_generic_coordinate hQ]; omega)

end Dubon2026.SourceEllipticVelu

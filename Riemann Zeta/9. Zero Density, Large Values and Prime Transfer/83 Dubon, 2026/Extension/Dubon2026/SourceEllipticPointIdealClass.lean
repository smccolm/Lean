import Dubon2026.SourceEllipticOddPointIdealNorm
import Dubon2026.SourceEllipticOddPointNorm

/-! The native affine point class represented by its actual nonzero integral
point ideal. This representation connects the proved point-ideal norm to
the existing additive norm point map, with no independent class witness
(DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The actual affine point ideal is nonzero because it contains the nonzero x-coordinate difference. -/
theorem XYIdeal_ne_zero (x y : F) : CoordinateRing.XYIdeal W x (C y) ≠ 0 := by
  intro hz
  have hm : CoordinateRing.XClass W x ∈ CoordinateRing.XYIdeal W x (C y) :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [hz, Ideal.zero_eq_bot, Ideal.mem_bot] at hm
  exact CoordinateRing.XClass_ne_zero x hm

/-- The actual point ideal, viewed in the monoid of nonzero integral ideals. -/
noncomputable def nonzeroPointIdeal (x y : F) : (Ideal W.CoordinateRing)⁰ :=
  ⟨CoordinateRing.XYIdeal W x (C y), mem_nonZeroDivisors_iff_ne_zero.mpr (XYIdeal_ne_zero W x y)⟩

/-- The integral representative has exactly the original two-generator point ideal. -/
theorem nonzeroPointIdeal_coe (x y : F) :
    (nonzeroPointIdeal W x y : Ideal W.CoordinateRing) = CoordinateRing.XYIdeal W x (C y) := rfl

variable [DecidableEq F] [IsDedekindDomain W.CoordinateRing]

/-- The native point class is the class of its actual nonzero integral point ideal. -/
theorem toMul_toClass_some_eq_mk0 {x y : F} (h : W.Nonsingular x y) :
    Additive.toMul (Point.some x y h).toClass = ClassGroup.mk0 (nonzeroPointIdeal W x y) := by
  rw [Point.toClass_some, ← ClassGroup.mk_mk0 W.FunctionField]
  apply congrArg (ClassGroup.mk W.FunctionField)
  apply Units.ext
  rfl

end Dubon2026.SourceEllipticFunctionField

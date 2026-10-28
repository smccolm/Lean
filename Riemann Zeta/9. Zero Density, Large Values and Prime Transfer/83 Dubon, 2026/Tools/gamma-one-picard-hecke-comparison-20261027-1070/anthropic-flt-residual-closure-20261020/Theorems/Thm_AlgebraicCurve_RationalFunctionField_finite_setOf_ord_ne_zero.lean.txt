import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero

open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero {K : Type*} [Field K] {f : RatFunc K} (hf : f ≠ 0) : {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.solution

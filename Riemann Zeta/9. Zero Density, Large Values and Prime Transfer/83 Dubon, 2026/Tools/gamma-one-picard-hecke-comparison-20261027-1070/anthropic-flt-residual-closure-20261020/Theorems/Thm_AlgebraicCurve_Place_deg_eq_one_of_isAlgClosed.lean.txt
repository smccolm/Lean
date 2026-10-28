import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed

open AlgebraicCurve

theorem AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F) (hv : v.deg ≠ 0) : v.deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed.solution

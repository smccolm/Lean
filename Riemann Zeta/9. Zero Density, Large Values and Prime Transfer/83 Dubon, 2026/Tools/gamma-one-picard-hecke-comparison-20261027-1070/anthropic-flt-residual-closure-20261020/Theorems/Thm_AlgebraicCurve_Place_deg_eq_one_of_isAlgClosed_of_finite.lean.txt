import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite
import Definitions.Def_AlgebraicCurve_IsCurveOver

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed_of_finite
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed_of_finite AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed_of_finite

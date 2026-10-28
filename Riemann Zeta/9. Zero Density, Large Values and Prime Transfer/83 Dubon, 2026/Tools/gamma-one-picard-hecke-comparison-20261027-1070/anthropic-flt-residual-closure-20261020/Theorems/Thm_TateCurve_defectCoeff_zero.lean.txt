import Mathlib
import Definitions.Def_TateCurve_Defect
import P2M.Util
import P2M.Sol.S_TateCurve_defectCoeff_zero

open TateCurve
open scoped NNReal
theorem TateCurve.defectCoeff_zero {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu1 : u ≠ 1) : defectCoeff u 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_defectCoeff_zero.solution

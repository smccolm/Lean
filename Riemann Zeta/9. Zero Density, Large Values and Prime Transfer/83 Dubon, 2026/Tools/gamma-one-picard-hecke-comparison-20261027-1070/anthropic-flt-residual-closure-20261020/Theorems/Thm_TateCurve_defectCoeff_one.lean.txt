import Definitions.Def_TateCurve_Defect
import P2M.Util
import P2M.Sol.S_TateCurve_defectCoeff_one

open TateCurve
open scoped NNReal
theorem TateCurve.defectCoeff_one {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) : defectCoeff u 1 = 0 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_defectCoeff_one.solution

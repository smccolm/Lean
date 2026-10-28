import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import P2M.Sol.S_TateCurve_nodal_xfun_yfun

open TateCurve
open scoped NNReal
theorem TateCurve.nodal_xfun_yfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw1 : w ≠ 1) : yfun w ^ 2 + xfun w * yfun w = xfun w ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_nodal_xfun_yfun.solution

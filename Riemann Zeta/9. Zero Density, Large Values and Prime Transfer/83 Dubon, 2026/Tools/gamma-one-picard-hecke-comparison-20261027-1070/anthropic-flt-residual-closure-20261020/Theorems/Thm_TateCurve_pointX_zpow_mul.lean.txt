import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import P2M.Sol.S_TateCurve_pointX_zpow_mul

open TateCurve
open scoped NNReal
theorem TateCurve.pointX_zpow_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (n : ℤ) : pointX q (q ^ n * u) = pointX q u := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_pointX_zpow_mul.solution

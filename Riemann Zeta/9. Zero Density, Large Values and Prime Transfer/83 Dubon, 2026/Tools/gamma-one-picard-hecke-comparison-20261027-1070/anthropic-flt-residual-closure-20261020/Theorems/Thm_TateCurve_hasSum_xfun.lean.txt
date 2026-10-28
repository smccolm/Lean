import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import P2M.Sol.S_TateCurve_hasSum_xfun

open TateCurve
open scoped NNReal
theorem TateCurve.hasSum_xfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw : ‖w‖₊ < 1) : HasSum (fun m : ℕ => ((m + 1 : ℕ) : K) * w ^ (m + 1)) (xfun w) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_hasSum_xfun.solution

import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import P2M.Sol.S_TateCurve_hasSum_yfun

open TateCurve
open scoped NNReal
theorem TateCurve.hasSum_yfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw : ‖w‖₊ < 1) : HasSum (fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2)) (yfun w) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_hasSum_yfun.solution

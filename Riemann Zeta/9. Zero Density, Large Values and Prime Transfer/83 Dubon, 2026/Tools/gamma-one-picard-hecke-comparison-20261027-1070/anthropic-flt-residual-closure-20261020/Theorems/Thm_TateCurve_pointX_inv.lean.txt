import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import P2M.Sol.S_TateCurve_pointX_inv

open TateCurve
open scoped NNReal
theorem TateCurve.pointX_inv {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointX q u⁻¹ = pointX q u := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_pointX_inv.solution

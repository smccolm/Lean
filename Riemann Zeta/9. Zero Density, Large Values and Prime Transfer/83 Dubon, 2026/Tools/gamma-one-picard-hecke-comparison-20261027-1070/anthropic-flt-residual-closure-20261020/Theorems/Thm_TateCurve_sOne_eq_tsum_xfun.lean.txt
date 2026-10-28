import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import P2M.Sol.S_TateCurve_sOne_eq_tsum_xfun

open TateCurve
open scoped NNReal
theorem TateCurve.sOne_eq_tsum_xfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : s₁ q = ∑' n : ℕ, xfun (q ^ (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_sOne_eq_tsum_xfun.solution

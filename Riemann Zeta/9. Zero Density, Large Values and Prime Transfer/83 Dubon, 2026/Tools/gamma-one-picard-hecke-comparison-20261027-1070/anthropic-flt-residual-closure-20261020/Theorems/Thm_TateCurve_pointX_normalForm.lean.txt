import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import P2M.Sol.S_TateCurve_pointX_normalForm

open TateCurve
open scoped NNReal
theorem TateCurve.pointX_normalForm {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointX q u = xfun u + ∑' n : ℕ, (xfun (q ^ (n + 1) * u) + xfun (q ^ (n + 1) * u⁻¹) - 2 * xfun (q ^ (n + 1))) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_pointX_normalForm.solution

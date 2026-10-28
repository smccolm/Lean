import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import P2M.Sol.S_TateCurve_pointY_normalForm

open TateCurve
open scoped NNReal
theorem TateCurve.pointY_normalForm {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointY q u = yfun u + ∑' n : ℕ, (yfun (q ^ (n + 1) * u) - yfun (q ^ (n + 1) * u⁻¹) - xfun (q ^ (n + 1) * u⁻¹) + xfun (q ^ (n + 1))) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_pointY_normalForm.solution

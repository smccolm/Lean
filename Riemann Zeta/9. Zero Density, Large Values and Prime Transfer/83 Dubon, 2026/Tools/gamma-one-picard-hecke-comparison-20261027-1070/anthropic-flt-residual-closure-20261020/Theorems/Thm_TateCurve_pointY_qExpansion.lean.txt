import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_TateCurve_Tails
import P2M.Util
import P2M.Sol.S_TateCurve_pointY_qExpansion

open TateCurve
open scoped NNReal
theorem TateCurve.pointY_qExpansion {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) : pointY q u = yfun u + ∑' N : ℕ, yCoeff u (N + 1) * q ^ (N + 1) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_pointY_qExpansion.solution

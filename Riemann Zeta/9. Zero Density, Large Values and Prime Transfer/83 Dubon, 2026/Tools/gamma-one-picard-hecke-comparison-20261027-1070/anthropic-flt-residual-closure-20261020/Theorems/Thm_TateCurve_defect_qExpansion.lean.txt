import Definitions.Def_TateCurve_Defect
import P2M.Util
import P2M.Sol.S_TateCurve_defect_qExpansion

open TateCurve
open scoped NNReal
theorem TateCurve.defect_qExpansion {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) : pointY q u ^ 2 + pointX q u * pointY q u - (pointX q u ^ 3 + a₄ q * pointX q u + a₆ q) = ∑' N : ℕ, defectCoeff u N * q ^ N := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_defect_qExpansion.solution

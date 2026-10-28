import Mathlib
import P2M.Util
import P2M.Sol.S_TateCurve_exists_zpow_mul_mem_annulus
open scoped NNReal
theorem TateCurve.exists_zpow_mul_mem_annulus {K : Type*} [NontriviallyNormedField K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) : ∃ n : ℤ, ‖q * (q ^ n * u)‖₊ < 1 ∧ ‖q * (q ^ n * u)⁻¹‖₊ < 1 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_exists_zpow_mul_mem_annulus.solution

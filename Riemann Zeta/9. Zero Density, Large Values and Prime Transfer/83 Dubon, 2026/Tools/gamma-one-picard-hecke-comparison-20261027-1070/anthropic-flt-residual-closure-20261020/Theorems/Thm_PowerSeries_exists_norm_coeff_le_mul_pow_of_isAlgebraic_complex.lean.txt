import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex

theorem PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex
    (φ : PowerSeries ℂ) (hφ : IsAlgebraic (Polynomial ℂ) φ) :
    ∃ C R : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n φ‖ ≤ C * R ^ n := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.solution

import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_isUnit_discriminant_and_c6_sq_eq_mul_X_sq_powerSeries

theorem WeierstrassCurve.exists_isUnit_discriminant_and_c6_sq_eq_mul_X_sq_powerSeries
    (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    ∃ E : WeierstrassCurve (PowerSeries K), IsUnit E.Δ ∧ E.c₆ ^ 2 = E.Δ * PowerSeries.X ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_isUnit_discriminant_and_c6_sq_eq_mul_X_sq_powerSeries.solution

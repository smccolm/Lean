import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic

theorem LaurentSeries.eq_C_coeff_zero_of_isAlgebraic {K : Type*} [Field K] {x : LaurentSeries K} (hx : IsAlgebraic K x) : x = HahnSeries.C (x.coeff 0) := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic.solution

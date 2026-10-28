import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed

open ModularCurve
theorem ModularCurve.pow_char_eq_qExpand_of_coeff_fixed {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (s : LaurentSeries R) (hfix : ∀ k : ℤ, (s.coeff k) ^ p = s.coeff k) :
    s ^ p = qExpand R p s := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.solution

import Mathlib.Algebra.Polynomial.Splits
import P2M.Util
import P2M.Sol.S_Polynomial_mem_range_of_eval_eq_const

theorem Polynomial.mem_range_of_eval_eq_const {F L : Type*} [Field F] [Field L] [Algebra F L] (g : Polynomial F) (x : L) (s : Finset L) (hcard : g.natDegree < s.card) (hval : ∀ y ∈ s, Polynomial.aeval y g = x) : x ∈ (algebraMap F L).range := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_mem_range_of_eval_eq_const.solution

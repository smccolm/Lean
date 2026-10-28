import Mathlib.Algebra.Polynomial.Splits
import P2M.Util
import P2M.Sol.S_Polynomial_mem_range_of_unique_common_root

theorem Polynomial.mem_range_of_unique_common_root {F L : Type*} [Field F] [Field L] [Algebra F L] (A B : Polynomial F) (hA : A ≠ 0) (hAs : (A.map (algebraMap F L)).Splits) (hAnd : (A.map (algebraMap F L)).roots.Nodup) (x : L) (hxA : Polynomial.aeval x A = 0) (hxB : Polynomial.aeval x B = 0) (huniq : ∀ y : L, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x) : x ∈ (algebraMap F L).range := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_mem_range_of_unique_common_root.solution

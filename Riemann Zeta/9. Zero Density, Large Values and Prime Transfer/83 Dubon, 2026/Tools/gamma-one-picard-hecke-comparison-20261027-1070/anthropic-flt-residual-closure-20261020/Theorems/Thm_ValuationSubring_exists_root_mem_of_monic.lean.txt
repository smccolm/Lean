import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_root_mem_of_monic

theorem ValuationSubring.exists_root_mem_of_monic {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_root_mem_of_monic.solution

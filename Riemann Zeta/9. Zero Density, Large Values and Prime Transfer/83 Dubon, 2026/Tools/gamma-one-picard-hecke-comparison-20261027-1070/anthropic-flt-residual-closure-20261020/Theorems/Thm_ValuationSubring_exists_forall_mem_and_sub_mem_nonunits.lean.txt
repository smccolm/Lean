import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits

theorem ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    {K : Type*} [Field K] {ι : Type*} [Finite ι] (R : ι → ValuationSubring K)
    (hR : ∀ i j, R i ≤ R j → i = j) (a : ι → K) (ha : ∀ i, a i ∈ R i) :
    ∃ z : K, ∀ i, z ∈ R i ∧ z - a i ∈ (R i).nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.solution

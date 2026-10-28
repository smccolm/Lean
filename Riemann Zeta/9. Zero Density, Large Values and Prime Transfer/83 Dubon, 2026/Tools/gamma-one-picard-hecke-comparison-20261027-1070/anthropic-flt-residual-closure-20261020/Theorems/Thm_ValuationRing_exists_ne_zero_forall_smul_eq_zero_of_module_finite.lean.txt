import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite

theorem ValuationRing.exists_ne_zero_forall_smul_eq_zero_of_module_finite
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ a : R, a ≠ 0 ∧ ∀ m : M, (∃ c : R, c ≠ 0 ∧ c • m = 0) → a • m = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite.solution

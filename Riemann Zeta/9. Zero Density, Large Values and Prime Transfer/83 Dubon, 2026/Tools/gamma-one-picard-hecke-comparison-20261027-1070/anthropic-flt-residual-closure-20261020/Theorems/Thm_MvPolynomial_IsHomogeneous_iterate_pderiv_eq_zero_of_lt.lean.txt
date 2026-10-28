import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt

set_option autoImplicit false

open scoped Manifold

theorem MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R}
    {n : ℕ} (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) :
    (MvPolynomial.pderiv k)^[i] φ = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.solution

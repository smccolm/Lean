import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CellDissection_euler_count_grid

theorem AlgebraicCurve.CellDissection.euler_count_grid (n J K np nc : ℕ) (g : ℤ) (hJK : np + nc = J * K)
    (ιc : Type*) [Fintype ιc] (hnc : Fintype.card ιc = nc)
    (fib : ιc → Type*) [∀ b, Fintype (fib b)] (ec : ∀ b, fib b → ℕ)
    (hec : ∀ b, ∑ w, ec b w = n)
    (ιp : Type*) [Fintype ιp] (ep : ιp → ℕ) (hep : ∑ q, ep q = n)
    (hRH : (∑ b, ∑ w, ((ec b w : ℤ) - 1)) + ∑ q, ((ep q : ℤ) - 1) = 2 * g - 2 + 2 * (n : ℤ)) :
    2 * ((n : ℤ) * ((J + 1) * (K + 1) + J * K + K)) -
        ((6 * n * np : ℤ) + (∑ b, ∑ w, (6 * ec b w : ℤ)) + ∑ q, ((ep q : ℤ) * (2 * J + 4 * K))) +
        2 * ((n * np : ℤ) + (∑ b, (Fintype.card (fib b) : ℤ)) + Fintype.card ιp) =
      2 * (2 - 2 * g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CellDissection_euler_count_grid.solution

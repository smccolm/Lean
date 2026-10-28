import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank

theorem Submodule.natCard_torsionBy_quotient_eq_pow_finrank
    {K : Type*} [DivisionRing K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L := by p2m_exact_reverting @_root_.P2MW.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.solution

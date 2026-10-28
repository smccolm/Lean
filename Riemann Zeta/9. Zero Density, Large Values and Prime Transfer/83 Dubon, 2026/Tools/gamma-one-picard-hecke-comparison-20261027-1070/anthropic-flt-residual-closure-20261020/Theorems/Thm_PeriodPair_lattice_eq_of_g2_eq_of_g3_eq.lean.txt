import Mathlib
import P2M.Util
import P2M.Sol.S_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq

theorem PeriodPair.lattice_eq_of_g2_eq_of_g3_eq (L L' : PeriodPair)
    (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq.solution

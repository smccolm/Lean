import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_jLattice_ofTau

open scoped UpperHalfPlane
theorem PeriodPair.jLattice_ofTau (τ : ℍ) :
    (PeriodPair.ofTau τ).jLattice = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_jLattice_ofTau.solution

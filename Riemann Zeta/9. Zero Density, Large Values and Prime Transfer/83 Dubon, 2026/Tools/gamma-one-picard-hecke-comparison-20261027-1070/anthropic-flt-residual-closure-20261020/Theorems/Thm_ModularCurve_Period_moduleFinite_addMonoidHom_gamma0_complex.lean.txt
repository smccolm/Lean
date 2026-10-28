import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex

set_option autoImplicit false
theorem ModularCurve.Period.moduleFinite_addMonoidHom_gamma0_complex (N : ℕ) [NeZero N] :
    Module.Finite ℂ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex.solution

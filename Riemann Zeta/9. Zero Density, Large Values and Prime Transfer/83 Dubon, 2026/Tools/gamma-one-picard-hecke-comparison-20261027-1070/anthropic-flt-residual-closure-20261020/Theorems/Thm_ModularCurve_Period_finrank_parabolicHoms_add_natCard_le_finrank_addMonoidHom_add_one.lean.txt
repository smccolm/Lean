import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one

set_option autoImplicit false
theorem ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K] :
    Module.finrank K (ModularCurve.Period.parabolicHoms K Γ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Module.finrank K (Additive Γ →+ K) + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.solution

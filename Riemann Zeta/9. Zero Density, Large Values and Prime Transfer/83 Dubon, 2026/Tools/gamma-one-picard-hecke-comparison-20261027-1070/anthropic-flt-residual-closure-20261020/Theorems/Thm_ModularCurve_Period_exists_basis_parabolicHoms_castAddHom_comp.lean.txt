import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.Basis.Defs
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (K : Type*) [Field K] [CharZero K],
        ∃ bK : Module.Basis (Fin n) K (ModularCurve.Period.parabolicHoms K Γ K),
          ∀ i, (bK i : Additive Γ →+ K) = (Int.castAddHom K).comp (b i : Additive Γ →+ ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp.solution

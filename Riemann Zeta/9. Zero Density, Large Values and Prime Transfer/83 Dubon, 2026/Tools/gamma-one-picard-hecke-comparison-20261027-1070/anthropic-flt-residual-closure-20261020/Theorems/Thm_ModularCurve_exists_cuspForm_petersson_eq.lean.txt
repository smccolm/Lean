import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_cuspForm_petersson_eq

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_petersson_eq {N : ℕ} [NeZero N]
    (ℓ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = ℓ g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_cuspForm_petersson_eq.solution

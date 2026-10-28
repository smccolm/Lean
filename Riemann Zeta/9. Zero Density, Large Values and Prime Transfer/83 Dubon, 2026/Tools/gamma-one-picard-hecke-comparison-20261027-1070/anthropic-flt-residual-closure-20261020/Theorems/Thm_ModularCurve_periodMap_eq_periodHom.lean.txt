import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_eq_periodHom

open scoped MatrixGroups
theorem ModularCurve.periodMap_eq_periodHom {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    {Fprim : UpperHalfPlane → ℂ} (hFprim : ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    ModularCurve.periodMap N f = hFprim.periodHom := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_eq_periodHom.solution

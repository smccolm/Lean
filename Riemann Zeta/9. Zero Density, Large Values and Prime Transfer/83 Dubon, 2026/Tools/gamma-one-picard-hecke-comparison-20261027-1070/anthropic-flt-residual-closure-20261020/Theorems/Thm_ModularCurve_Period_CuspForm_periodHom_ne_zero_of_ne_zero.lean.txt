import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero

open scoped MatrixGroups
theorem ModularCurve.Period.CuspForm.periodHom_ne_zero_of_ne_zero {N : ℕ} [NeZero N]
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f ≠ 0)
    {Fprim : UpperHalfPlane → ℂ} (hFprim : ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    hFprim.periodHom ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero.solution

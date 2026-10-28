import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt

open scoped MatrixGroups
theorem ModularCurve.Period.IsEquivariantPrimitive.periodHom_eq_of_hasDerivAt {Γ : Subgroup SL(2, ℤ)}
    {F G : UpperHalfPlane → ℂ} {f : UpperHalfPlane → ℂ}
    (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F) (hG : ModularCurve.Period.IsEquivariantPrimitive Γ G)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (F ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ)
    (hGf : ∀ τ : UpperHalfPlane, HasDerivAt (G ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    hF.periodHom = hG.periodHom := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt.solution

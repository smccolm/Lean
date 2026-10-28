import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom

open scoped MatrixGroups
theorem ModularCurve.Period.IsEquivariantPrimitive.isParabolicHom_periodHom {Γ : Subgroup SL(2, ℤ)}
    {F : UpperHalfPlane → ℂ} (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Filter.Tendsto (fun w : UpperHalfPlane => F (δ • w)) UpperHalfPlane.atImInfty (nhds L)) :
    ModularCurve.Period.IsParabolicHom Γ hF.periodHom := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom.solution

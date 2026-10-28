import Definitions.Def_ModularCurve_HahnSpecialise
import P2M.Util
import P2M.Sol.S_ModularCurve_HahnSpecialise_specialiseCycSub_injective

open ModularCurve ModularCurve.B3 ModularCurve.HahnSpecialise
open ModularCurve.TatePoint (Qbar H CycSubH)
open scoped Classical

theorem ModularCurve.HahnSpecialise.specialiseCycSub_injective (E : WeierstrassCurve H) (hE : IntegralCoeffs E)
    (hΔ : (specialFibre E).Δ ≠ 0) (N : ℕ) [NeZero N] :
    Function.Injective (specialiseCycSub E hE hΔ N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_HahnSpecialise_specialiseCycSub_injective.solution

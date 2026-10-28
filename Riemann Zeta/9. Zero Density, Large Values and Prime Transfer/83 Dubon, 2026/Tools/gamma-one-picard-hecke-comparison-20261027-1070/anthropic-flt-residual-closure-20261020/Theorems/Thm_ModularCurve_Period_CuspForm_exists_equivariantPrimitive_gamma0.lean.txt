import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0

open scoped MatrixGroups
theorem ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∃ Fprim : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) ∧
      Filter.Tendsto Fprim UpperHalfPlane.atImInfty (nhds 0) ∧
      ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim ∧
      ∀ δ : SL(2, ℤ), ∃ L : ℂ,
        Filter.Tendsto (fun w : UpperHalfPlane => Fprim (δ • w)) UpperHalfPlane.atImInfty (nhds L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0.solution

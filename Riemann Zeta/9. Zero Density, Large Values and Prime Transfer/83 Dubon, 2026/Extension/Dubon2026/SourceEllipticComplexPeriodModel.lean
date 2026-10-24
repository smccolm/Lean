import Dubon2026.SourceEllipticPeriodModularCurve
import Dubon2026.SourceAnalyticJSurjectivity
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-! Every actual complex elliptic curve is isomorphic, by a native change of
variables, to an actual period curve. The j-value is supplied by the proved
surjectivity theorem; no uniformization or moduli certificate is assumed.
This supplies the complex model needed for the odd-prime quotient product,
and hence the DUB-17/18 cyclic-root and inertia obligations. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve
open Dubon2026.SourceFunctionField

theorem exists_complex_period_model (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (τ : UpperHalfPlane) (C : VariableChange ℂ),
      C • periodCurve (PeriodLattice.ofTau τ) = W := by
  obtain ⟨τ, hτ⟩ := JMultiplicity.jf_surjective W.j
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _
    ((periodCurve_ofTau_j τ).trans hτ)
  exact ⟨τ, C, hC⟩

end Dubon2026.SourceEllipticPeriod

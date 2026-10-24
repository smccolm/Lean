import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-! The actual elliptic equation attached to a native period pair. Mathlib's
Weierstrass differential equation supplies its analytic points. This is the
complex-analytic link required to identify the actual odd quotient factors
with the integral modular polynomial, then obtain cyclic roots and the
DUB-17/18 inertia census. Uniformization and that identity are not assumed.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_PeriodPair_Uniformization.lean. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve
open scoped PeriodPair
noncomputable section

/-- The actual short Weierstrass equation determined by the period invariants. -/
def periodCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

theorem periodCurve_discriminant (L : PeriodPair) :
    (periodCurve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, periodCurve]
  ring

theorem periodCurve_cFour (L : PeriodPair) : (periodCurve L).c₄ = 12 * L.g₂ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, periodCurve]
  ring

/-- The native Weierstrass functions satisfy this actual affine equation. -/
theorem periodCurve_equation (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    (periodCurve L).toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := L.derivWeierstrassP_sq z hz
  change (℘'[L] z / 2) ^ 2 + 0 * ℘[L] z * (℘'[L] z / 2) + 0 * (℘'[L] z / 2) =
    ℘[L] z ^ 3 + 0 * ℘[L] z ^ 2 + (-L.g₂ / 4) * ℘[L] z + (-L.g₃ / 4)
  linear_combination (1 / 4 : ℂ) * h

end
end Dubon2026.SourceEllipticPeriod

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! DUB-17/18 -> original torsion cardinality -> Abel converse and discrete
periods -> raw geometric reciprocity -> analytic cell dissection. These are
the source radial cells with positive periodic piecewise C2 boundary radius.
Adapted from Def_AlgebraicCurve_CellDissection, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
open Set Complex
open scoped Real

/-- The actual radial planar region and its finite smooth boundary arcs. -/
structure RadialRegion where
  /-- The center of the radial region. -/
  q : ℂ
  /-- The positive periodic boundary radius. -/
  r : ℝ → ℝ
  hcont : Continuous r
  hper : Function.Periodic r (2 * π)
  hpos : ∀ φ, 0 < r φ
  /-- The number of smooth boundary arcs. -/
  N : ℕ
  /-- The increasing angular endpoints of the boundary arcs. -/
  φs : Fin (N + 1) → ℝ
  hφ0 : φs 0 = 0
  hφN : φs (Fin.last N) = 2 * π
  hmono : StrictMono φs
  hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Icc (φs i.castSucc) (φs i.succ))

namespace RadialRegion
/-- The closed region bounded by the prescribed radial loop. -/
def K (R : RadialRegion) : Set ℂ := {z | ‖z - R.q‖ ≤ R.r (arg (z - R.q))}
/-- The strict radial interior of the source cell. -/
def Kint (R : RadialRegion) : Set ℂ := {z | ‖z - R.q‖ < R.r (arg (z - R.q))}
/-- The actual positively oriented radial boundary parameterization. -/
noncomputable def loop (R : RadialRegion) (φ : ℝ) : ℂ := R.q + R.r φ * exp (φ * I)
/-- The formal boundary derivative, valid on each smooth arc. -/
noncomputable def loop' (R : RadialRegion) (φ : ℝ) : ℂ :=
  (((deriv R.r φ : ℝ) : ℂ) + R.r φ * I) * exp (φ * I)
/-- The closed parameter interval of a source boundary arc. -/
def arcIcc (R : RadialRegion) (k : Fin R.N) : Set ℝ := Icc (R.φs k.castSucc) (R.φs k.succ)
/-- The actual image of a source boundary arc. -/
def arcSet (R : RadialRegion) (k : Fin R.N) : Set ℂ := R.loop '' R.arcIcc k
end RadialRegion
end Dubon2026.SourceFunctionField.CellGeometry

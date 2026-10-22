import Dubon2026.SourceCellRadialInterior
import Dubon2026.SourceOriginalChartDifferentials

/-! DUB-17/18 -> raw geometric reciprocity -> analytic cell dissection.
Analytic cell coordinates are actual open partial homeomorphisms on the
original complex place manifold, with holomorphic nonsingular transitions.
The manifold topology and charts are the already constructed original ones.
Adapted from Def_AlgebraicCurve_CellDissection, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
open scoped Manifold ContDiff
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace

/-- A genuine analytic coordinate on the original complex place manifold. -/
structure AnalyticCoord (N : ℕ) [NeZero N] where
  /-- The actual open coordinate homeomorphism. -/
  ζ : OpenPartialHomeomorph (Place ℂ (modularFunctionFieldOver N ℂ)) ℂ
  analytic : ∀ P ∈ ζ.source,
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P)
  deriv_ne : ∀ P ∈ ζ.source,
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0

variable {N : ℕ} [NeZero N]

/-- The original field element evaluated in a genuine cell coordinate. -/
def AnalyticCoord.read (A : AnalyticCoord N) (f : modularFunctionFieldOver N ℂ) : ℂ → ℂ :=
  fun z => originalPlaceEval N ℂ (A.ζ.symm z) f

/-- The coefficient of an actual original differential in an open coordinate. -/
def coeffIn (ζ : OpenPartialHomeomorph (Place ℂ (modularFunctionFieldOver N ℂ)) ℂ)
    (θ : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) (w : ℂ) : ℂ :=
  OriginalChart.readDifferential N (ζ.symm w) θ
      (extChartAt 𝓘(ℂ, ℂ) (ζ.symm w) (ζ.symm w)) *
    deriv (extChartAt 𝓘(ℂ, ℂ) (ζ.symm w) ∘ ζ.symm) w

end
end Dubon2026.SourceFunctionField.CellGeometry

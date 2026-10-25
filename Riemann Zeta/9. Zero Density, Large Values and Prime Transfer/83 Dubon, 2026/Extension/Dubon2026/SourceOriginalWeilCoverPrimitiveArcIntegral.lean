import Dubon2026.SourceOriginalWeilCoverBoundaryCoefficient
import Dubon2026.SourceCellArcIntegralExtension

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
The proved continuous boundary coefficient and native continuous extension
give arc integrability. Native FTC then identifies actual coordinate integrals
with endpoint differences of the constructed regular cell primitives. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology Interval
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders

theorem cover_arc_integrable :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N) (θ : Ω[EE⁄ℂ]),
      (∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) →
      IntervalIntegrable (coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders C θ)
        MeasureTheory.volume (C.R.φs k.castSucc) (C.R.φs k.succ) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C hC k θ hθ
  have hgd := (cover_continuousOn_boundary_coefficient N n radicand baseDivisor hRadicand hOrders C hC k θ hθ).mul
    (C.R.continuous_loopDerivOnArc k).continuousOn
  refine (arc_integral_eq_of_continuous_extension (C.R.hmono Fin.castSucc_lt_succ).le hgd ?_).1
  intro s hs
  change CF C.ζ θ (C.R.loop s) * C.R.loop' s = _
  rw [C.R.loop'_eq_loopDerivOnArc k hs]
  rfl

theorem cover_primitive_arc_integral :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N) (θ : Ω[EE⁄ℂ]) {V : Set ℂ}, C.R.K ⊆ V →
      ∀ {Ψ : ℂ → ℂ}, (∀ w ∈ V, HasDerivAt Ψ (CF C.ζ θ w) w) →
      (∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) →
      (∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ),
        coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders C θ s) =
      Ψ (C.R.loop (C.R.φs k.succ)) - Ψ (C.R.loop (C.R.φs k.castSucc)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C hC k θ V hKV Ψ hΨ hθ
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (C.R.hmono Fin.castSucc_lt_succ).le
    (f := fun s => Ψ (C.R.loop s))
  · intro s _
    exact ((hΨ _ (hKV (C.R.loop_mem_K s))).continuousAt.comp
      C.R.continuous_loop.continuousAt).continuousWithinAt
  · intro s hs
    exact (hΨ _ (hKV (C.R.loop_mem_K s))).comp s (C.R.hasDerivAt_loop k hs)
  · exact cover_arc_integrable N n radicand baseDivisor hRadicand hOrders C hC k θ hθ

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

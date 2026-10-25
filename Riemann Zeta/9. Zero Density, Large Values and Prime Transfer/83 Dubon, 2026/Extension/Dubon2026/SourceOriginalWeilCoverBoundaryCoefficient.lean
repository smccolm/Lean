import Dubon2026.SourceOriginalWeilCoverCellCoefficientPullback
import Dubon2026.SourceRadialCellBoundaryCoordinates

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
The actual boundary integrand uses the proved cover differential coefficient.
Its coefficient is continuous on every arc where the differential is regular,
including the endpoints. This supplies the continuous extension used by FTC. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology
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

/-- The actual differential coefficient evaluated on the radial boundary. -/
def coverBoundaryIntegrand :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    RadialCell (Place ℂ EE) → Ω[EE⁄ℂ] → ℝ → ℂ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun C θ s => CF C.ζ θ (C.R.loop s) * C.R.loop' s

theorem cover_continuousOn_boundary_coefficient :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N) (θ : Ω[EE⁄ℂ]),
      (∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) →
      ContinuousOn (fun s => CF C.ζ θ (C.R.loop s)) (C.R.arcIcc k) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C hC k θ hθ s hs
  obtain ⟨hQ, hval⟩ := C.bdry_coordinates s
  have ha := (cover_coeff_eq_near N n radicand baseDivisor hRadicand hOrders C.ζ hQ
    (hC _ hQ).1 (hC _ hQ).2 θ ((C.bdry s).mem_of_ord_nonneg (hθ s hs))).2
  rw [hval] at ha
  exact (ha.continuousAt.comp C.R.continuous_loop.continuousAt).continuousWithinAt

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

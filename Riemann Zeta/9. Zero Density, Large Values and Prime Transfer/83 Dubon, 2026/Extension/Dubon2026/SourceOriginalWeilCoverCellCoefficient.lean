import Dubon2026.SourceOriginalWeilCoverCoordinateInverse
import Dubon2026.SourceOriginalWeilCoverOneFormLaw

/-! DUB-17/18 -> cover reciprocity -> coordinate edge integrals and primitives.
The coefficient is the actual centered differential reading transformed by
the inverse cell coordinate. Its local calculus is proved in the next module. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

/-- Actual differential coefficient in the supplied open cover coordinate. -/
def coverCoeffIn :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    OpenPartialHomeomorph (Place ℂ EE) ℂ → Ω[EE⁄ℂ] → ℂ → ℂ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun ζ θ w =>
    readDifferential N n radicand baseDivisor hRadicand hOrders (ζ.symm w) θ 0 *
      deriv (placeChart N n radicand baseDivisor hRadicand hOrders (ζ.symm w) ∘ ζ.symm) w

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

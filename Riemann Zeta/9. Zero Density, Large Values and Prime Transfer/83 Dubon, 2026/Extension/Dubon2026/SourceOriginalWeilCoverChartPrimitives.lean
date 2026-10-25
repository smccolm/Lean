import Dubon2026.SourceOriginalWeilCoverDifferentialRegularity
import Mathlib.Analysis.Complex.HasPrimitives

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel comparison.
Adapt the proved original-curve coordinate and primitive arguments to the
literal Kummer cover, using its constructed charts and finite coordinate.
The primitive gluing argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem exists_readDifferential_primitive_on_chart
    (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE)) :
    ∃ Φ : ℂ → ℂ, ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA v),
      HasDerivAt Φ (readDifferential N n r A hr hrA v ω z) z :=
  (analyticOnNhd_readDifferential N n r A hr hrA v ω hω).differentiableOn.isExactOn_ball


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

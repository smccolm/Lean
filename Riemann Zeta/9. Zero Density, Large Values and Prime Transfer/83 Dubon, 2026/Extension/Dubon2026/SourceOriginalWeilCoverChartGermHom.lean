import Dubon2026.SourceOriginalWeilCoverDifferentialReadings
import Mathlib.Order.Filter.Germ.Basic

/-! DUB-17/18 -> auxiliary Abel comparison -> actual differential readings.
Adapt the existing original-curve residue-germ derivation argument to the
literal Kummer splitting field and its constructed uniformizer charts.
The local spanning and field-reading inputs are proved for this actual cover.
The original derivation proof was adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

/-- The actual cover function field evaluated in a punctured uniformizer germ. -/
def chartReadHom (v : Place ℂ (EE)) :
    EE →+* Germ (𝓝[≠] (0 : ℂ)) ℂ where
  toFun f := (chartRead N n r A hr hrA v f : Germ (𝓝[≠] (0 : ℂ)) ℂ)
  map_one' := by rw [chartRead_one, Germ.coe_one]
  map_zero' := by rw [chartRead_zero, Germ.coe_zero]
  map_add' f g := by
    rw [← Germ.coe_add]
    exact Germ.coe_eq.mpr (chartRead_add N n r A hr hrA v f g)
  map_mul' f g := by
    rw [← Germ.coe_mul]
    exact Germ.coe_eq.mpr (chartRead_mul N n r A hr hrA v f g)

theorem chartReadHom_apply (v : Place ℂ (EE))
    (f : EE) :
    chartReadHom N n r A hr hrA v f = (chartRead N n r A hr hrA v f : Germ (𝓝[≠] (0 : ℂ)) ℂ) := rfl

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

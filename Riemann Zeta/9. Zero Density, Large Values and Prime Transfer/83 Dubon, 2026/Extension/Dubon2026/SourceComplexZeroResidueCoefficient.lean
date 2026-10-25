import Dubon2026.SourceComplexResidueSubtractedCoefficient

/-! DUB-17/18 -> cover Abel converse -> pole-avoiding logarithmic primitive atlas.
When the residue vanishes and the original coefficient is continuous, its
removable-limit filling agrees with that coefficient, including the center. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Filter
open scoped Topology

theorem residueSubtractedCoefficient_zero (q : ℂ) (f : ℂ → ℂ) {w : ℂ}
    (hf : ContinuousAt f w) : residueSubtractedCoefficient q 0 f w = f w := by
  by_cases hw : w = q
  · subst w
    simp only [residueSubtractedCoefficient, Function.update_self, zero_div, sub_zero]
    exact (hf.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  · rw [residueSubtractedCoefficient_of_ne q 0 f hw, zero_div, sub_zero]

end
end Dubon2026.SourceFunctionField.CellGeometry

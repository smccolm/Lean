import Dubon2026.AlgebraicLocalIntegerAction
import Mathlib.NumberTheory.LocalField.Basic

/-! The actual norm residue field is finite for the original locally
compact nonarchimedean field. This removes the residue finiteness input
from DUB-17's local inertia dimension assembly. -/

namespace Dubon2026
noncomputable section
open scoped NNReal

/-- Local compactness of the original normed field makes its actual
norm-valuation residue field finite. -/
theorem normLocal_residue_finite (K : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [LocallyCompactSpace K] :
    Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)) := by
  letI : Valued K ℝ≥0 := NormedField.toValued
  letI : (Valued.v (R := K) (Γ₀ := ℝ≥0)).RankOne :=
    inferInstanceAs (NormedField.valuation (K := K)).RankOne
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K ℝ≥0
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact ((Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := K) (Γ₀ := ℝ≥0)).mp
    (inferInstance : ProperSpace K)).2.2

end
end Dubon2026

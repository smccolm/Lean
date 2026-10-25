import Dubon2026.SourceCurveFiniteCoordinateOnePole
import Dubon2026.SourceOriginalWeilKummerGeometry

/-! DUB-17/18 -> auxiliary connectedness -> actual algebraic inputs.
The literal Kummer splitting field has the proved finite transcendental
coordinate. It therefore has places and a nonconstant function regular
away from any specified place, without an index or Riemann-Roch premise.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial IntermediateField
variable (N : ℕ) [NeZero N] (n : ℕ) (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])

theorem nonempty_cover_place : Nonempty (Place ℂ EE) := by
  obtain ⟨ht, hfin⟩ := originalWeilKummerCover_finite_coordinate N ℂ n f
  letI := hfin
  exact nonempty_place_of_separating_coordinate (algebraMap FF EE (jOver N ℂ)) ht

theorem exists_cover_nonconstant_regular_away (v : Place ℂ EE) :
    ∃ a : EE, a ∉ Set.range (algebraMap ℂ EE) ∧
      ∀ w : Place ℂ EE, w ≠ v → a ∈ w.toValuationSubring := by
  obtain ⟨ht, hfin⟩ := originalWeilKummerCover_finite_coordinate N ℂ n f
  letI := hfin
  exact exists_nonconstant_regular_away_of_finite_coordinate
    (algebraMap FF EE (jOver N ℂ)) ht v

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

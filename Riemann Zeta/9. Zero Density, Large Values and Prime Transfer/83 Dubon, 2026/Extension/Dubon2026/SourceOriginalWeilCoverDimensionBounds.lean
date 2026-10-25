import Dubon2026.SourceCurveFiniteCoordinateDimensionBounds
import Dubon2026.SourceOriginalWeilKummerGeometry

/-! DUB-17/18 -> cover Abel converse -> actual meromorphic field comparison.
Instantiate the existing finite-coordinate geometry for the literal Kummer
field. Its finite divisor spaces and natural degree-dimension bound provide
the pole-clearing and independent-basis inputs, without a genus assumption.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial IntermediateField
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C r : Polynomial FF)

theorem finite_cover_lSpace (Q : Place ℂ EE) (D : Divisor ℂ EE) :
    Module.Finite ℂ (LSpace D) := by
  letI := originalWeilKummerCover_curve N ℂ n r
  letI : ∀ v : Place ℂ EE, Module.Finite ℂ v.ResidueField :=
    (originalWeilKummerCover_curve N ℂ n r).finiteResidue
  letI := finite_lSpace_zero_of_place Q
  exact finite_lSpace D

theorem exists_cover_degree_dimension_bound :
    ∃ g : ℕ, ∀ D : Divisor ℂ EE, Divisor.degree D + 1 - g ≤ (ell D : ℤ) := by
  obtain ⟨ht, hfin⟩ := originalWeilKummerCover_finite_coordinate N ℂ n r
  letI := hfin
  exact exists_natural_degree_dimension_bound (algebraMap FF EE (jOver N ℂ)) ht

theorem exists_cover_pole_clearing_function (Q : Place ℂ EE) (D : Divisor ℂ EE) :
    ∃ k : ℕ, ∃ a : EE, a ≠ 0 ∧ a ∈ LSpace (Finsupp.single Q (k : ℤ) - D) := by
  obtain ⟨ht, hfin⟩ := originalWeilKummerCover_finite_coordinate N ℂ n r
  letI := hfin
  exact exists_pole_clearing_function_of_finite_coordinate
    (algebraMap FF EE (jOver N ℂ)) ht Q D

theorem cover_one_place_dimension_sum_gt (Q : Place ℂ EE) (g k : ℕ)
    (hg : ∀ D : Divisor ℂ EE, Divisor.degree D + 1 - g ≤ (ell D : ℤ)) :
    k + 2 * g + 1 < ell (Finsupp.single Q ((k + 2 * g : ℕ) : ℤ)) +
      ell (Finsupp.single Q ((2 * g : ℕ) : ℤ)) := by
  letI := (originalWeilKummerCover_finite_coordinate N ℂ n r).2
  exact one_place_dimension_sum_gt_of_bound (algebraMap FF EE (jOver N ℂ)) Q g k hg

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

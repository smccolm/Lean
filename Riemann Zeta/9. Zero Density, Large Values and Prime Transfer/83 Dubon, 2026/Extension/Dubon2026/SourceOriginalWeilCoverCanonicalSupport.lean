import Dubon2026.SourceOriginalWeilCoverDimensionBounds
import Dubon2026.SourceOriginalWeilCoverOnePole
import Dubon2026.SourceOriginalWeilCoverLocalDifferentials
import Dubon2026.SourceCurveFiniteCoordinateCanonical

/-! DUB-17/18 -> auxiliary point division -> cover Jacobi inversion.
The existing finite-coordinate canonical support theorem supplies finite
support of actual differentials. Its canonical divisor space identifies
the actual regular differentials with an already finite divisor space.
No numerical genus or period rank is needed for this finite basis input. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

omit [NeZero N] in
theorem cover_coordinate_differential_ne_zero :
    D ℂ EE (algebraMap FF EE (jOver N ℂ)) ≠ 0 :=
  D_algebraMap_ne_zero_of_separable (D_jOver_ne_zero N ℂ)

theorem finite_cover_differential_support {ω : Ω[EE⁄ℂ]} (hω : ω ≠ 0) :
    {v : Place ℂ EE | v.ordDifferential ω ≠ 0}.Finite := by
  letI := (originalWeilKummerCover_finite_coordinate N ℂ n r).2
  exact finite_coordinate_differential_support (algebraMap FF EE (jOver N ℂ))
    (originalWeilKummerCover_finite_coordinate N ℂ n r).1
    (cover_coordinate_differential_ne_zero N n r) hω

theorem finite_cover_regularDifferentials : Module.Finite ℂ (regularDifferentials ℂ EE) := by
  letI := (originalWeilKummerCover_finite_coordinate N ℂ n r).2
  letI := originalWeilKummerCover_curve N ℂ n r
  letI := hasCanonicalDivisor_finite_coordinate (algebraMap FF EE (jOver N ℂ))
    (originalWeilKummerCover_finite_coordinate N ℂ n r).1
    (cover_coordinate_differential_ne_zero N n r)
  letI : ∀ v : Place ℂ EE, v.DCoordGenerates := cover_place_dCoordGenerates N n r
  letI := cover_differentials_nontrivial N n r
  let Q : Place ℂ EE := Classical.choice (nonempty_cover_place N n r)
  letI := finite_cover_lSpace N n r Q
    (canonicalDivisorOf (cover_coordinate_differential_ne_zero N n r))
  exact Module.Finite.equiv (RegularDifferentialsComparison.lSpaceCanonicalEquivRegular
    (cover_coordinate_differential_ne_zero N n r))

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

import Dubon2026.SourceCurveFiniteCoordinateUnramifiedGenus
import Dubon2026.SourceOriginalWeilCoverCanonicalSupport
import Dubon2026.SourceCurveUnramifiedCanonicalDegree
import Dubon2026.SourceOriginalWeilEveryLocalCover

/-! DUB-17/18 -> lifted dissection reciprocity -> exact cover Euler genus.
The already proved unramified canonical-degree pullback and finite-coordinate
residue duality give the genus multiplicity for the literal cover, using the
actual regular-differential dimensions. No topological or genus formula is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve IntermediateField KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem cover_euler_genus_multiplicity :
    2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ EE) : ℤ) =
      (Module.finrank FF EE : ℤ) * (2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ FF) : ℤ)) := by
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  letI := finiteDimensional_original N ℂ
  letI := (originalWeilKummerCover_finite_coordinate N ℂ n radicand).2
  exact finite_coordinate_euler_genus_of_unramified (jOver N ℂ)
    (transcendental_jOver N ℂ) (D_jOver_ne_zero N ℂ)
    (originalWeilKummerCover_finite_coordinate N ℂ n radicand).1
    (cover_coordinate_differential_ne_zero N n radicand)
    (OriginalChart.originalWeil_complex_kummer_unramified N n radicand baseDivisor hRadicand hOrders)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

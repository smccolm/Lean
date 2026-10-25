import Dubon2026.SourceOriginalWeilCoverClassDivision
import Dubon2026.SourceOriginalWeilKummerPointDifference

/-! DUB-17/18 -> actual finite Weil detection. Apply the proved cover class
division to the exact point difference used by the NYLL norm-detection route.
The radicand has n-divisible orders, precisely as supplied by the actual
nonzero original torsion class; general ramified covers are unnecessary. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)


theorem cover_point_difference_has_division (σ : EE ≃ₐ[FF] EE) (w : Place ℂ EE) :
    ∃ y : Pic0 ℂ EE, n • y = Pic0.mk (originalWeilKummerPointDifference N ℂ n radicand σ w) :=
  cover_degree_zero_class_has_division N n radicand baseDivisor hRadicand hOrders w
    (originalWeilKummerPointDifference N ℂ n radicand σ w)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

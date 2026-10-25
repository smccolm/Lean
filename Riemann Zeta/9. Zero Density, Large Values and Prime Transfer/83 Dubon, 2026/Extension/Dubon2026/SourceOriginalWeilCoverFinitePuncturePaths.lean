import Dubon2026.SourceChartFinitePuncturePaths
import Dubon2026.SourceOriginalWeilCoverConnected
import Dubon2026.SourceOriginalWeilCoverRegularEvaluationSeparation

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> global meromorphic exponential. Reuse the native logarithmic-model and finite-puncture arguments with proved cover geometry and actual residue values. The global period correction remains open. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)

theorem exists_cover_place_outside_finite {S : Set (Place ℂ EE)} (hS : S.Finite) :
    ∃ v, v ∉ S := by
  letI := place_infinite N n radicand A hRadicand hOrders
  exact hS.exists_notMem

theorem cover_isPathConnected_compl_finite {S : Set (Place ℂ EE)} (hS : S.Finite) :
    letI := placeTopology N n radicand A hRadicand hOrders
    IsPathConnected Sᶜ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  letI := placeChartedSpace N n radicand A hRadicand hOrders
  letI := place_t2Space N n radicand A hRadicand hOrders
  letI := place_connectedSpace N n radicand A hRadicand hOrders
  exact OriginalExpTopology.isPathConnected_compl_of_finite hS
    (exists_cover_place_outside_finite N n radicand A hRadicand hOrders hS)


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

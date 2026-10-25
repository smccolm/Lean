import Dubon2026.SourceOriginalWeilCoverDifferentialReadings
import Dubon2026.SourceOriginalWeilCoverReadFieldLaws

/-! DUB-17/18 -> cover period-matrix injectivity. The existing faithful
function reading and local differential coordinate show that a vanishing
actual differential germ forces the algebraic differential to be zero. -/
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


theorem eq_zero_of_readDifferential_eventually_eq_zero (v : Place ℂ EE)
    (ω : Ω[EE⁄ℂ])
    (hω : ∀ᶠ z in 𝓝 (0 : ℂ), readDifferential N n radicand baseDivisor hRadicand hOrders v ω z = 0) :
    ω = 0 := by
  letI := cover_place_dCoordGenerates N n radicand v
  have hc : v.differentialCoeff ω = 0 := by
    apply eq_zero_of_chartRead_eventuallyEq_zero N n radicand baseDivisor hRadicand hOrders v
    filter_upwards [hω.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (place_spec N n radicand baseDivisor hRadicand hOrders v).1)] with z hz hzb
    rwa [readDifferential_eq_coefficient N n radicand baseDivisor hRadicand hOrders v ω hzb] at hz
  rw [← v.differentialCoeff_smul_dCoord ω, hc, zero_smul]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

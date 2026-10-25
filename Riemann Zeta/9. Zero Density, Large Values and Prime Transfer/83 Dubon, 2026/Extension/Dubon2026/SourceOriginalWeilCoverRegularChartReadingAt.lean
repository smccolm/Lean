import Dubon2026.SourceOriginalWeilCoverLocalRegularPrimitives

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period principality. The native exponential argument is applied to the actual cover with constructed residue data, paths and local models. Integral loop periods remain an explicit upstream hypothesis; their correction and the full Abel converse are not asserted here. -/
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


theorem analyticAt_readDifferential_at_of_coeff_mem (v : Place ℂ EE) (η : Ω[EE⁄ℂ])
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n radicand A hRadicand hOrders v))
    (hη : (placeFamily N n radicand A hRadicand hOrders v z).differentialCoeff η ∈
      (placeFamily N n radicand A hRadicand hOrders v z).toValuationSubring) :
    AnalyticAt ℂ (readDifferential N n radicand A hRadicand hOrders v η) z := by
  letI := placeTopology N n radicand A hRadicand hOrders
  have hc := chart_differentialCoeff_regular_at N n radicand A hRadicand hOrders v (placeFamily N n radicand A hRadicand hOrders v z) η hη ⟨z, hz, rfl⟩
  have ha : AnalyticAt ℂ (chartRead N n radicand A hRadicand hOrders v (v.differentialCoeff η)) z :=
    (place_spec N n radicand A hRadicand hOrders v).2.2.1.analyticAt hz hc
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds hz] with u hu
  exact (readDifferential_eq_coefficient N n radicand A hRadicand hOrders v η hu).symm


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

import Dubon2026.SourceOriginalLocalRegularPrimitives

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. Regularity at an actual place in a chart
gives analyticity of the differential reading at its coordinate. This is
the input to local primitives away from the prescribed finite pole support.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem analyticAt_readDifferential_at_of_coeff_mem (v : Place ℂ F) (η : Ω[F⁄ℂ])
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v))
    (hη : (placeFamily N v z).differentialCoeff η ∈
      (placeFamily N v z).toValuationSubring) :
    AnalyticAt ℂ (readDifferential N v η) z := by
  have hc := chart_differentialCoeff_regular_at N v (placeFamily N v z) η hη ⟨z, hz, rfl⟩
  have ha : AnalyticAt ℂ (chartRead N v (v.differentialCoeff η)) z :=
    (place_spec N v).2.2.1.analyticAt hz hc
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds hz] with u hu
  exact (readDifferential_eq_coefficient N v η hu).symm

end
end Dubon2026.SourceFunctionField.OriginalChart

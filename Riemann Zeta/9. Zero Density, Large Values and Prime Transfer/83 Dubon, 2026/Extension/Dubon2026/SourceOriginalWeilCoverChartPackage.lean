import Dubon2026.SourceOriginalWeilCoverParameter
import Dubon2026.SourceCurveAnalyticChartOrders

/-! DUB-17/18 -> auxiliary cover Abel comparison -> compatible analytic charts.
The literal cover parameter theorem supplies exact reading orders and
order-one uniformizer differences. These are the proved inputs of the
uniformizer-division branch-comparison theorem. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])

theorem exists_parameter_package (D : Divisor ℂ FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (w : Place ℂ EE) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ EE), 0 < ρ ∧ γ 0 = w ∧
      AnalyticChart.Orders (originalWeilKummerCover_residue_bijective N ℂ n f) γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ,
        (γ z).ord (w.uniformizer - algebraMap ℂ EE z) = 1) := by
  obtain ⟨ρ, γ, hρ, h0, _, heval, ho⟩ :=
    OriginalChart.exists_originalWeil_cover_parameter N n f D hf hfD w
  refine ⟨ρ, γ, hρ, h0, ho, ?_⟩
  intro z hz
  exact AnalyticChart.Orders.uniformizer_sub_order ho (Metric.isOpen_ball.mem_nhds hz) w heval

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

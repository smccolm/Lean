import Dubon2026.SourceOriginalChartDifferentialRegularity
import Mathlib.Analysis.Complex.HasPrimitives

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> actual path periods.
A finite family of original regular differentials has analytic primitives
on one disk inside each actual uniformizer chart. Existing local regularity
and the native disk-primitive theorem discharge every existence input.
This is the local input to gluing primitives along actual continuous paths.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem exists_readDifferential_primitive_on_chart
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ Φ : ℂ → ℂ, ∀ z ∈ ball (0 : ℂ) (placeRadius N v),
      HasDerivAt Φ (readDifferential N v ω z) z :=
  (analyticOnNhd_readDifferential N v ω hω).differentiableOn.isExactOn_ball

theorem exists_original_regular_chart_primitives {n : ℕ}
    (ω : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ∀ i, ω i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ r : ℝ, 0 < r ∧ r < placeRadius N v ∧
      (∀ i, ∀ z ∈ ball (0 : ℂ) r,
        v.differentialCoeff (ω i) ∈ (placeFamily N v z).toValuationSubring) ∧
      ∃ Φ : Fin n → ℂ → ℂ, ∀ i, ∀ z ∈ ball (0 : ℂ) r,
        HasDerivAt (Φ i) (readDifferential N v (ω i) z) z := by
  have hr := (place_spec N v).1
  have hsub : ball (0 : ℂ) (placeRadius N v / 2) ⊆ ball 0 (placeRadius N v) :=
    ball_subset_ball (half_le_self hr.le)
  refine ⟨placeRadius N v / 2, half_pos hr, half_lt_self hr,
    fun i z hz => chart_differentialCoeff_regular N v (ω i) (hω i) (hsub hz), ?_⟩
  choose Φ hΦ using fun i => exists_readDifferential_primitive_on_chart N v (ω i) (hω i)
  exact ⟨Φ, fun i z hz => hΦ i z (hsub hz)⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

import Dubon2026.SourceOriginalChartFiberData
import Dubon2026.SourceOriginalLocalDifferentials

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi
-> path periods of actual regular differentials. Read the original
Kaehler differential in its actual uniformizer chart. The existing chart
identity makes the uniformizer derivative one, so regularity gives the
required analytic coefficient without another formal-coordinate choice.
The product formula follows Definitions/Def_AlgebraicCurve_ComplexLineIntegral
in anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology Manifold
variable (N : ℕ) [NeZero N]

/-- Literal original residue evaluation in the constructed uniformizer chart. -/
def chartRead (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) : ℂ → ℂ :=
  fun z => originalPlaceEval N ℂ (placeFamily N v z) f

/-- The actual original differential coefficient times the coordinate derivative. -/
def readDifferential (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) : ℂ → ℂ :=
  fun z => chartRead N v (v.differentialCoeff ω) z * deriv (chartRead N v v.uniformizer) z

theorem chartRead_eq_extChartAt (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) (z : ℂ) :
    (letI := placeTopology N; letI := placeChartedSpace N;
      originalPlaceEval N ℂ ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) = chartRead N v f z := by
  letI := placeTopology N
  letI := placeChartedSpace N
  rw [extPlaceChart_symm_apply]
  rfl

theorem chartRead_uniformizer (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) : chartRead N v v.uniformizer z = z :=
  place_eval_uniformizer N v hz

theorem deriv_chartRead_uniformizer (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) : deriv (chartRead N v v.uniformizer) z = 1 := by
  have he : chartRead N v v.uniformizer =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    exact chartRead_uniformizer N v hu
  rw [he.deriv_eq]
  exact deriv_id z

theorem readDifferential_eq_coefficient (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) :
    readDifferential N v ω z = chartRead N v (v.differentialCoeff ω) z := by
  rw [readDifferential, deriv_chartRead_uniformizer N v hz, mul_one]

theorem analyticAt_readDifferential (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    AnalyticAt ℂ (readDifferential N v ω) 0 := by
  have hc := (mem_original_regularDifferentials_iff N ℂ ω).mp hω v
  have ha : AnalyticAt ℂ (chartRead N v (v.differentialCoeff ω)) 0 :=
    analyticAt_place_reading N v hc
  apply ha.congr
  filter_upwards [ball_mem_nhds (0 : ℂ) (place_spec N v).1] with z hz
  exact (readDifferential_eq_coefficient N v ω hz).symm

end
end Dubon2026.SourceFunctionField.OriginalChart

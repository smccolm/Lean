import Dubon2026.SourceOriginalWeilCoverReadFieldLaws
import Dubon2026.SourceOriginalWeilCoverLocalDifferentials

/-! DUB-17/18 -> auxiliary Abel comparison -> actual differential readings.
Adapt the existing original-curve residue-germ derivation argument to the
literal Kummer splitting field and its constructed uniformizer charts.
The local spanning and field-reading inputs are proved for this actual cover.
The original derivation proof was adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology Manifold
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

/-- The actual cover differential coefficient times the coordinate derivative. -/
def readDifferential (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ]) : ℂ → ℂ :=
  fun z => chartRead N n r A hr hrA v (v.differentialCoeff ω) z * deriv (chartRead N n r A hr hrA v v.uniformizer) z

theorem chartRead_uniformizer (v : Place ℂ (EE))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) : chartRead N n r A hr hrA v v.uniformizer z = z :=
  place_eval_uniformizer N n r A hr hrA v hz

theorem deriv_chartRead_uniformizer (v : Place ℂ (EE))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) : deriv (chartRead N n r A hr hrA v v.uniformizer) z = 1 := by
  have he : chartRead N n r A hr hrA v v.uniformizer =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    exact chartRead_uniformizer N n r A hr hrA v hu
  rw [he.deriv_eq]
  exact deriv_id z

theorem readDifferential_eq_coefficient (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ]) {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) :
    readDifferential N n r A hr hrA v ω z = chartRead N n r A hr hrA v (v.differentialCoeff ω) z := by
  rw [readDifferential, deriv_chartRead_uniformizer N n r A hr hrA v hz, mul_one]

theorem analyticAt_readDifferential (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE)) :
    AnalyticAt ℂ (readDifferential N n r A hr hrA v ω) 0 := by
  have hc := (mem_cover_regularDifferentials_iff N n r ω).mp hω v
  have ha : AnalyticAt ℂ (chartRead N n r A hr hrA v (v.differentialCoeff ω)) 0 :=
    analyticAt_place_reading N n r A hr hrA v hc
  apply ha.congr
  filter_upwards [ball_mem_nhds (0 : ℂ) (place_spec N n r A hr hrA v).1] with z hz
  exact (readDifferential_eq_coefficient N n r A hr hrA v ω hz).symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

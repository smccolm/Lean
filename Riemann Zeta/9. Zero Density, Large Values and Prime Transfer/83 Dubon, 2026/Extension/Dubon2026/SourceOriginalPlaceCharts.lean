import Dubon2026.SourceOriginalAllChartPackage

/-! DUB-17/18 -> original torsion cardinality -> global complex charts.
The actual uniformizer parameter at every original place supplies its
partial chart. Existing residue and order identities prove the inverse
laws. This family covers all places, including the proved cusp family.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve
open scoped Topology
variable (N : ℕ) [NeZero N]

/-- The radius supplied by the proved original all-place parameter theorem. -/
def placeRadius (v : Place ℂ (modularFunctionFieldOver N ℂ)) : ℝ :=
  (original_place_parameter_package N v).choose

/-- The actual original place family supplied by the proved all-place parameter theorem. -/
def placeFamily (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ℂ → Place ℂ (modularFunctionFieldOver N ℂ) :=
  (original_place_parameter_package N v).choose_spec.choose

theorem place_spec (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    0 < placeRadius N v ∧ placeFamily N v 0 = v ∧
      Orders N (placeFamily N v) (Metric.ball 0 (placeRadius N v)) ∧
      (∀ z ∈ Metric.ball 0 (placeRadius N v), (placeFamily N v z).ord
        (v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) z) = 1) :=
  (original_place_parameter_package N v).choose_spec.choose_spec

theorem place_eval_uniformizer (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {z : ℂ}
    (hz : z ∈ Metric.ball 0 (placeRadius N v)) :
    originalPlaceEval N ℂ (placeFamily N v z) v.uniformizer = z :=
  originalPlaceEval_eq_of_ord_sub_pos N ℂ (placeFamily N v z) v.uniformizer z
    (by rw [(place_spec N v).2.2.2 z hz]; norm_num)

/-- The actual all-place partial chart, with the original uniformizer as coordinate. -/
def placeChart (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    PartialEquiv (Place ℂ (modularFunctionFieldOver N ℂ)) ℂ where
  toFun w := originalPlaceEval N ℂ w v.uniformizer
  invFun := placeFamily N v
  source := placeFamily N v '' Metric.ball 0 (placeRadius N v)
  target := Metric.ball 0 (placeRadius N v)
  map_source' := by
    rintro w ⟨z, hz, rfl⟩
    rw [place_eval_uniformizer N v hz]
    exact hz
  map_target' := fun z hz => ⟨z, hz, rfl⟩
  left_inv' := by
    rintro w ⟨z, hz, rfl⟩
    rw [place_eval_uniformizer N v hz]
  right_inv' := fun z hz => place_eval_uniformizer N v hz

theorem placeChart_source (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    (placeChart N v).source = placeFamily N v '' Metric.ball 0 (placeRadius N v) := rfl

theorem placeChart_target (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    (placeChart N v).target = Metric.ball 0 (placeRadius N v) := rfl

theorem mem_placeChart_source (v : Place ℂ (modularFunctionFieldOver N ℂ)) : v ∈ (placeChart N v).source :=
  ⟨0, Metric.mem_ball_self (place_spec N v).1, (place_spec N v).2.1⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

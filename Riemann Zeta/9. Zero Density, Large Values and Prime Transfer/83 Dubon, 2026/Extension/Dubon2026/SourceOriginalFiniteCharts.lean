import Dubon2026.SourceOriginalChartBranchEquality

/-! DUB-17/18 -> original torsion cardinality -> actual complex-place
charts. Select the proved uniformizer parameter for each actual finite
place and construct its genuine partial equivalence with a complex disk.
The inverse identities are proved from the original residue evaluation.
This is a finite-place chart family; cusp coverage is still required.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve
open scoped Topology
variable (N : ℕ) [NeZero N]

/-- The radius supplied by the proved original finite-place parameter theorem. -/
def finiteRadius (v : Place ℂ (modularFunctionFieldOver N ℂ)) (hv : jOver N ℂ ∈ v.toValuationSubring) : ℝ :=
  (original_finite_place_parameter_package N v hv).choose

/-- The actual original place family supplied by the proved finite-place parameter theorem. -/
def finiteFamily (v : Place ℂ (modularFunctionFieldOver N ℂ)) (hv : jOver N ℂ ∈ v.toValuationSubring) :
    ℂ → Place ℂ (modularFunctionFieldOver N ℂ) :=
  (original_finite_place_parameter_package N v hv).choose_spec.choose

theorem finite_spec (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (hv : jOver N ℂ ∈ v.toValuationSubring) :
    0 < finiteRadius N v hv ∧ finiteFamily N v hv 0 = v ∧
      Orders N (finiteFamily N v hv) (Metric.ball 0 (finiteRadius N v hv)) ∧
      (∀ z ∈ Metric.ball 0 (finiteRadius N v hv), (finiteFamily N v hv z).ord
        (v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) z) = 1) :=
  (original_finite_place_parameter_package N v hv).choose_spec.choose_spec

theorem finite_eval_uniformizer (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (hv : jOver N ℂ ∈ v.toValuationSubring) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (finiteRadius N v hv)) :
    originalPlaceEval N ℂ (finiteFamily N v hv z) v.uniformizer = z :=
  originalPlaceEval_eq_of_ord_sub_pos N ℂ (finiteFamily N v hv z) v.uniformizer z
    (by rw [(finite_spec N v hv).2.2.2 z hz]; norm_num)

/-- The actual finite-place partial chart, with the original uniformizer as coordinate. -/
def finiteChart (v : Place ℂ (modularFunctionFieldOver N ℂ)) (hv : jOver N ℂ ∈ v.toValuationSubring) :
    PartialEquiv (Place ℂ (modularFunctionFieldOver N ℂ)) ℂ where
  toFun w := originalPlaceEval N ℂ w v.uniformizer
  invFun := finiteFamily N v hv
  source := finiteFamily N v hv '' Metric.ball 0 (finiteRadius N v hv)
  target := Metric.ball 0 (finiteRadius N v hv)
  map_source' := by
    rintro w ⟨z, hz, rfl⟩
    rw [finite_eval_uniformizer N v hv hz]
    exact hz
  map_target' := fun z hz => ⟨z, hz, rfl⟩
  left_inv' := by
    rintro w ⟨z, hz, rfl⟩
    rw [finite_eval_uniformizer N v hv hz]
  right_inv' := fun z hz => finite_eval_uniformizer N v hv hz

theorem finiteChart_source (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (hv : jOver N ℂ ∈ v.toValuationSubring) :
    (finiteChart N v hv).source = finiteFamily N v hv '' Metric.ball 0 (finiteRadius N v hv) := rfl

theorem finiteChart_target (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (hv : jOver N ℂ ∈ v.toValuationSubring) :
    (finiteChart N v hv).target = Metric.ball 0 (finiteRadius N v hv) := rfl

theorem mem_finiteChart_source (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (hv : jOver N ℂ ∈ v.toValuationSubring) : v ∈ (finiteChart N v hv).source :=
  ⟨0, Metric.mem_ball_self (finite_spec N v hv).1, (finite_spec N v hv).2.1⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

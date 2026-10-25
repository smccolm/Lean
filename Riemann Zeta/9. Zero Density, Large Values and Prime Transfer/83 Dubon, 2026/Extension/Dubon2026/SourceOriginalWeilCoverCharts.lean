import Dubon2026.SourceOriginalWeilCoverChartPackage

/-! DUB-17/18 -> auxiliary cover Abel comparison -> actual partial charts.
Choose the already proved parameter family at every place of the literal
Kummer cover. Its actual residue coordinate gives the inverse partial chart.
No chart family, inverse law or local order property is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

/-- Radius of the proved parameter at the specified actual cover place. -/
def placeRadius (v : Place ℂ EE) : ℝ :=
  (exists_parameter_package N n f D hf hfD v).choose

/-- The actual cover place family supplied by the proved parameter theorem. -/
def placeFamily (v : Place ℂ EE) : ℂ → Place ℂ EE :=
  (exists_parameter_package N n f D hf hfD v).choose_spec.choose

theorem place_spec (v : Place ℂ EE) :
    0 < placeRadius N n f D hf hfD v ∧ placeFamily N n f D hf hfD v 0 = v ∧
      AnalyticChart.Orders (originalWeilKummerCover_residue_bijective N ℂ n f)
        (placeFamily N n f D hf hfD v) (Metric.ball 0 (placeRadius N n f D hf hfD v)) ∧
      (∀ z ∈ Metric.ball 0 (placeRadius N n f D hf hfD v),
        (placeFamily N n f D hf hfD v z).ord (v.uniformizer - algebraMap ℂ EE z) = 1) :=
  (exists_parameter_package N n f D hf hfD v).choose_spec.choose_spec

theorem place_eval_uniformizer (v : Place ℂ EE) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (placeRadius N n f D hf hfD v)) :
    (placeFamily N n f D hf hfD v z).rationalEval
      (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z))
      v.uniformizer = z :=
  (placeFamily N n f D hf hfD v z).rationalEval_eq_of_ord_sub_pos _ v.uniformizer z
    (by rw [(place_spec N n f D hf hfD v).2.2.2 z hz]; norm_num)

/-- Partial chart with the actual cover uniformizer as residue coordinate. -/
def placeChart (v : Place ℂ EE) : PartialEquiv (Place ℂ EE) ℂ where
  toFun w := w.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f w) v.uniformizer
  invFun := placeFamily N n f D hf hfD v
  source := placeFamily N n f D hf hfD v '' Metric.ball 0 (placeRadius N n f D hf hfD v)
  target := Metric.ball 0 (placeRadius N n f D hf hfD v)
  map_source' := by
    rintro w ⟨z, hz, rfl⟩
    rw [place_eval_uniformizer N n f D hf hfD v hz]
    exact hz
  map_target' := fun z hz => ⟨z, hz, rfl⟩
  left_inv' := by
    rintro w ⟨z, hz, rfl⟩
    rw [place_eval_uniformizer N n f D hf hfD v hz]
  right_inv' := fun z hz => place_eval_uniformizer N n f D hf hfD v hz

theorem placeChart_source (v : Place ℂ EE) :
    (placeChart N n f D hf hfD v).source =
      placeFamily N n f D hf hfD v '' Metric.ball 0 (placeRadius N n f D hf hfD v) := rfl

theorem placeChart_target (v : Place ℂ EE) :
    (placeChart N n f D hf hfD v).target = Metric.ball 0 (placeRadius N n f D hf hfD v) := rfl

theorem mem_placeChart_source (v : Place ℂ EE) : v ∈ (placeChart N n f D hf hfD v).source :=
  ⟨0, Metric.mem_ball_self (place_spec N n f D hf hfD v).1, (place_spec N n f D hf hfD v).2.1⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

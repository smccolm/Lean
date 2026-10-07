import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The actual Sato–Tate angle probability and coefficient distribution

This constructs the classical measure; it asserts no arithmetic equidistribution theorem.
-/

namespace Dubon2026

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

/-- The classical nonnegative angle density 2 sin² θ / π. -/
def satoTateAngleDensity (θ : ℝ) : ℝ := (2 / Real.pi) * Real.sin θ ^ 2

theorem satoTateAngleDensity_nonneg (θ : ℝ) : 0 ≤ satoTateAngleDensity θ := by
  unfold satoTateAngleDensity
  positivity

theorem continuous_satoTateAngleDensity : Continuous satoTateAngleDensity := by
  unfold satoTateAngleDensity
  fun_prop

theorem integral_satoTateAngleDensity :
    (∫ θ in Icc 0 Real.pi, satoTateAngleDensity θ) = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  simp only [satoTateAngleDensity, intervalIntegral.integral_const_mul, integral_sin_sq,
    Real.sin_zero, Real.sin_pi, zero_mul, sub_zero, zero_add]
  field_simp

/-- Density 2 sin² θ / π on the actual interval [0,π]. -/
def satoTateAngleMeasure : Measure ℝ :=
  (volume.restrict (Icc 0 Real.pi)).withDensity (fun θ => ENNReal.ofReal (satoTateAngleDensity θ))

instance satoTateAngleMeasure_isProbabilityMeasure : IsProbabilityMeasure satoTateAngleMeasure := by
  constructor
  rw [satoTateAngleMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (continuous_satoTateAngleDensity.integrableOn_Icc)
      (Eventually.of_forall satoTateAngleDensity_nonneg), integral_satoTateAngleDensity]
  exact ENNReal.ofReal_one

/-- The angle law bundled with its proved total mass one. -/
def satoTateAngleProbability : ProbabilityMeasure ℝ := ⟨satoTateAngleMeasure, inferInstance⟩

/-- The coefficient law is the pushforward of the angle law under θ ↦ 2 cos θ. -/
def satoTateProbability : ProbabilityMeasure ℝ :=
  satoTateAngleProbability.map (show Measurable (fun θ : ℝ => 2 * Real.cos θ) by fun_prop).aemeasurable

theorem satoTateProbability_singleton (x : ℝ) : (satoTateProbability : Measure ℝ) {x} = 0 := by
  change Measure.map (fun θ : ℝ => 2 * Real.cos θ) satoTateAngleMeasure {x} = 0
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply ((show Measurable (fun θ : ℝ => 2 * Real.cos θ) by fun_prop) (measurableSet_singleton x))]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply Real.injOn_cos ha.2 hb.2
  have ha' : 2 * Real.cos a = x := ha.1
  have hb' : 2 * Real.cos b = x := hb.1
  linarith

instance satoTateProbability_noAtoms : NoAtoms (satoTateProbability : Measure ℝ) :=
  ⟨satoTateProbability_singleton⟩

/-- The literal selected coefficient band. -/
def satoTateBand : Set ℝ := Icc (-2) (-1) ∪ Icc 1 2

theorem mem_satoTateBand {x : ℝ} : x ∈ satoTateBand ↔ 1 ≤ |x| ∧ |x| ≤ 2 := by
  simp only [satoTateBand, mem_union, mem_Icc]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    constructor
    · rintro (h | h)
      · linarith
      · exact h
    · exact Or.inr
  · rw [abs_of_nonpos (le_of_not_ge hx)]
    constructor
    · rintro (h | h)
      · constructor <;> linarith
      · linarith
    · intro h
      left
      constructor <;> linarith

theorem measurableSet_satoTateBand : MeasurableSet satoTateBand :=
  measurableSet_Icc.union measurableSet_Icc

theorem satoTateBand_null_frontier :
    (satoTateProbability : Measure ℝ) (frontier satoTateBand) = 0 := by
  apply measure_mono_null (frontier_union_subset _ _)
  apply measure_union_null
  · apply measure_mono_null inter_subset_left
    rw [frontier_Icc (by norm_num : (-2 : ℝ) ≤ -1)]
    exact ((Set.countable_singleton (-1 : ℝ)).insert (-2)).measure_zero _
  · apply measure_mono_null inter_subset_right
    rw [frontier_Icc (by norm_num : (1 : ℝ) ≤ 2)]
    exact ((Set.countable_singleton (2 : ℝ)).insert 1).measure_zero _


theorem satoTateAngleMeasure_Ioo_pos {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi)
    (hab : a < b) : 0 < satoTateAngleMeasure (Ioo a b) := by
  have hs : Ioo a b ⊆ Icc 0 Real.pi := fun x hx =>
    ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩
  have hi : IntegrableOn satoTateAngleDensity (Ioo a b) :=
    continuous_satoTateAngleDensity.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [satoTateAngleMeasure, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hs,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall satoTateAngleDensity_nonneg)]
  apply ENNReal.ofReal_pos.mpr
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall satoTateAngleDensity_nonneg) hi).mpr
  have hsub : Ioo a b ⊆ Function.support satoTateAngleDensity := by
    intro x hx
    have hx0 : 0 < x := ha.trans_lt hx.1
    have hxpi : x < Real.pi := hx.2.trans_le hb
    have hp := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
    change satoTateAngleDensity x ≠ 0
    exact ne_of_gt (mul_pos (div_pos (by norm_num) Real.pi_pos) (sq_pos_of_pos hp))
  rw [inter_eq_right.mpr hsub, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

theorem satoTateBand_pos : 0 < (satoTateProbability : Measure ℝ) satoTateBand := by
  change 0 < Measure.map (fun θ : ℝ => 2 * Real.cos θ) satoTateAngleMeasure satoTateBand
  rw [Measure.map_apply (by fun_prop) measurableSet_satoTateBand]
  apply (satoTateAngleMeasure_Ioo_pos (a := 0) (b := Real.pi / 3)
    le_rfl (by linarith [Real.pi_pos]) (by positivity)).trans_le
  apply measure_mono
  intro x hx
  change 2 * Real.cos x ∈ satoTateBand
  have hc := Real.antitoneOn_cos
    (show x ∈ Icc 0 Real.pi from ⟨hx.1.le, by linarith [Real.pi_pos, hx.2]⟩)
    (show Real.pi / 3 ∈ Icc 0 Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩) hx.2.le
  rw [Real.cos_pi_div_three] at hc
  apply mem_satoTateBand.mpr
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * Real.cos x)]
  constructor
  · linarith
  · linarith [Real.cos_le_one x]

end

end Dubon2026

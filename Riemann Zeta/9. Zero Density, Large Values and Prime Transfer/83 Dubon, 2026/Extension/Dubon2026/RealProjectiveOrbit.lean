import Dubon2026.RealCentralQuotient
import Dubon2026.RealCyclicL2

/-! # The actual projective orbit map and its hyperbolic pushforward -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory
open scoped MatrixGroups

/-- The actual scalar signs act trivially on the original upper half-plane. -/
theorem realSL2_center_smul (c : SL(2, ℝ))
    (hc : c ∈ Subgroup.center SL(2, ℝ)) (z : ℍ) : c • z = z := by
  rcases (realSL2_center_eq_signs c).mp hc with rfl | rfl
  · exact one_smul _ z
  · change mapGL ℝ (-1 : SL(2, ℝ)) • z = z
    have he : mapGL ℝ (-1 : SL(2, ℝ)) = -1 := by
      ext i j
      simp [mapGL, Matrix.SpecialLinearGroup.map, toGL, coe_neg]
    rw [he, neg_smul, one_smul]

/-- The genuine orbit of i, descended through the actual central quotient. -/
def realProjectiveOrbit : PSL(2, ℝ) → ℍ :=
  Quotient.lift (fun g : SL(2, ℝ) => g • I) (by
    intro a b hab
    change a • I = b • I
    rw [show b = a * (a⁻¹ * b) by group, mul_smul,
      realSL2_center_smul _ (QuotientGroup.leftRel_apply.mp hab)])

/-- Evaluating the quotient orbit at an actual representative gives its original orbit. -/
theorem realProjectiveOrbit_mk (g : SL(2, ℝ)) :
    realProjectiveOrbit (QuotientGroup.mk g) = g • I := rfl

/-- The actual projective orbit map is continuous. -/
theorem realProjectiveOrbit_continuous : Continuous realProjectiveOrbit :=
  (continuous_id.smul continuous_const).quotient_lift _

/-- The descended orbit intertwines genuine left multiplication and the original real action. -/
theorem realProjectiveOrbit_mul (a : SL(2, ℝ)) (q : PSL(2, ℝ)) :
    realProjectiveOrbit (QuotientGroup.mk a * q) = a • realProjectiveOrbit q := by
  induction q using Quotient.inductionOn with | h g => ?_
  change (a * g) • I = a • g • I
  exact mul_smul a g I

/-- The original real orbit pushes the proved Haar measure exactly to hyperbolic area. -/
theorem realGroupOrbit_measurePreserving :
    MeasurePreserving (fun g : SL(2, ℝ) => g • I) realGroupMeasure (volume : Measure ℍ) := by
  refine ⟨(continuous_id.smul continuous_const).measurable, ?_⟩
  rw [realGroupMeasure, Measure.map_map (by fun_prop)
    realIwasawaHomeomorph.symm.continuous.measurable]
  have he : (fun g : SL(2, ℝ) => g • I) ∘ realIwasawaHomeomorph.symm = Prod.fst := by
    funext p
    exact realIwasawa_orbit p.1 p.2
  rw [he]
  exact (measurePreserving_fst (μ := (volume : Measure ℍ)) (ν := realCompactHaar)).map_eq

/-- The actual projective Haar measure has the same exact hyperbolic orbit pushforward. -/
theorem realProjectiveOrbit_measurePreserving :
    MeasurePreserving realProjectiveOrbit realProjectiveMeasure (volume : Measure ℍ) := by
  refine ⟨realProjectiveOrbit_continuous.measurable, ?_⟩
  rw [realProjectiveMeasure, Measure.map_map realProjectiveOrbit_continuous.measurable
    QuotientGroup.continuous_mk.measurable]
  exact realGroupOrbit_measurePreserving.map_eq

/-- The genuine projective compact fiber has exactly the hyperbolic mass of its base set. -/
theorem realProjectiveMeasure_base_fiber (S : Set ℍ) (hS : MeasurableSet S) :
    realProjectiveMeasure (realProjectiveOrbit ⁻¹' S) = volume S :=
  realProjectiveOrbit_measurePreserving.measure_preimage hS.nullMeasurableSet

end
end Dubon2026

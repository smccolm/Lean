import Dubon2026.RealIwasawa
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! # The actual invariant real-group measure in Iwasawa coordinates -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory
open scoped MatrixGroups

instance realSpecialLinearMeasurableSpace : MeasurableSpace SL(2, ℝ) := borel _

instance realSpecialLinear_borelSpace : BorelSpace SL(2, ℝ) := ⟨rfl⟩

instance realCompactSubgroup_compactSpace : CompactSpace realCompactSubgroup :=
  isCompact_iff_compactSpace.mp realCompactSubgroup_isCompact

/-- The genuine compact Haar probability, normalized on the entire original stabilizer. -/
def realCompactHaar : Measure realCompactSubgroup :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance realCompactHaar_isHaarMeasure : realCompactHaar.IsHaarMeasure :=
  inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure _))

instance realCompactHaar_isProbabilityMeasure : IsProbabilityMeasure realCompactHaar :=
  ⟨Measure.haarMeasure_self⟩

/-- The actual left compact cocycle is multiplicative in the original right compact coordinate. -/
theorem realIwasawaCompact_mul_compact (a : SL(2, ℝ)) (z : ℍ) (h : realCompactSubgroup) :
    realIwasawaCompact (a * (z.toSL2R * h.val)) =
      realIwasawaCompact (a * z.toSL2R) * h := by
  apply Subtype.ext
  change (((a * (z.toSL2R * h.val)) • I).toSL2R)⁻¹ * (a * (z.toSL2R * h.val)) =
    (((a * z.toSL2R) • I).toSL2R)⁻¹ * (a * z.toSL2R) * h.val
  rw [mul_smul a, realIwasawa_orbit, mul_smul a, toSL2R_smul_I]
  group

/-- The original left group action becomes the actual compact cocycle over the hyperbolic action. -/
theorem realIwasawa_left_action (a : SL(2, ℝ)) (z : ℍ) (h : realCompactSubgroup) :
    a * realIwasawaHomeomorph.symm (z, h) =
      realIwasawaHomeomorph.symm (a • z, realIwasawaCompact (a * z.toSL2R) * h) := by
  have he := realIwasawa_reconstruct (a * z.toSL2R)
  rw [mul_smul, toSL2R_smul_I] at he
  change a * (z.toSL2R * h.val) =
    (a • z).toSL2R * ((realIwasawaCompact (a * z.toSL2R)).val * h.val)
  calc
    _ = (a * z.toSL2R) * h.val := (mul_assoc _ _ _).symm
    _ = ((a • z).toSL2R * (realIwasawaCompact (a * z.toSL2R)).val) * h.val :=
      congrArg (fun t => t * h.val) he.symm
    _ = _ := mul_assoc _ _ _

/-- Hyperbolic volume and genuine compact Haar probability are pushed through the actual Iwasawa homeomorphism. -/
def realGroupMeasure : Measure SL(2, ℝ) :=
  Measure.map realIwasawaHomeomorph.symm ((volume : Measure ℍ).prod realCompactHaar)

/-- The actual Iwasawa reconstruction preserves the constructed product measure. -/
theorem realIwasawa_measurePreserving : MeasurePreserving realIwasawaHomeomorph.symm
    ((volume : Measure ℍ).prod realCompactHaar) realGroupMeasure :=
  ⟨realIwasawaHomeomorph.symm.continuous.measurable, rfl⟩

/-- The genuine left compact cocycle preserves the actual hyperbolic-times-Haar product measure. -/
theorem realIwasawa_cocycle_measurePreserving (a : SL(2, ℝ)) :
    MeasurePreserving (fun p : ℍ × realCompactSubgroup =>
      (a • p.1, realIwasawaCompact (a * p.1.toSL2R) * p.2))
      ((volume : Measure ℍ).prod realCompactHaar)
      ((volume : Measure ℍ).prod realCompactHaar) := by
  have ha : MeasurePreserving (fun z : ℍ => a • z) volume volume :=
    measurePreserving_smul (mapGL ℝ a) volume
  apply ha.skew_product (μc := realCompactHaar) (μd := realCompactHaar)
    (g := fun z h => realIwasawaCompact (a * z.toSL2R) * h)
  · exact ((realIwasawaCompact_continuous.comp
      (continuous_const.mul (continuous_toSL2R.comp continuous_fst))).mul continuous_snd).measurable
  · exact Filter.Eventually.of_forall (fun z =>
      (measurePreserving_mul_left realCompactHaar (realIwasawaCompact (a * z.toSL2R))).map_eq)

/-- Every original left real-group translation preserves the genuine Iwasawa measure. -/
theorem realGroupMeasure_left_invariant (a : SL(2, ℝ)) :
    MeasurePreserving (fun g : SL(2, ℝ) => a * g) realGroupMeasure realGroupMeasure := by
  have hh := realIwasawa_measurePreserving.comp (realIwasawa_cocycle_measurePreserving a)
  refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
  rw [realGroupMeasure, Measure.map_map (by fun_prop) realIwasawaHomeomorph.symm.continuous.measurable]
  convert hh.map_eq using 1
  congr 1
  funext p
  exact realIwasawa_left_action a p.1 p.2

instance realGroupMeasure_isMulLeftInvariant : realGroupMeasure.IsMulLeftInvariant :=
  ⟨fun g => (realGroupMeasure_left_invariant g).map_eq⟩

instance realGroupMeasure_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts realGroupMeasure :=
  Measure.IsFiniteMeasureOnCompacts.map ((volume : Measure ℍ).prod realCompactHaar)
    realIwasawaHomeomorph.symm

instance realGroupMeasure_isOpenPosMeasure : realGroupMeasure.IsOpenPosMeasure :=
  realIwasawaHomeomorph.symm.continuous.isOpenPosMeasure_map realIwasawaHomeomorph.symm.surjective

/-- The constructed actual Iwasawa measure is a genuine Haar measure on the real group. -/
instance realGroupMeasure_isHaarMeasure : realGroupMeasure.IsHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsMulLeftInvariant := inferInstance
  toIsOpenPosMeasure := inferInstance

end
end Dubon2026

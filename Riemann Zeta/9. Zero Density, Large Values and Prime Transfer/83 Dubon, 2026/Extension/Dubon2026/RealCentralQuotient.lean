import Dubon2026.RealGroupUnimodular
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # The actual real central quotient and its pushed Haar measure -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups Pointwise

/-- The center of the actual real determinant-one group consists precisely of the two signs. -/
theorem realSL2_center_eq_signs (g : SL(2, ℝ)) :
    g ∈ Subgroup.center SL(2, ℝ) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    obtain ⟨r, hr, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    simp only [Fintype.card_fin] at hr
    have hs : r = 1 ∨ r = -1 := by
      rcases mul_eq_zero.mp (by nlinarith [hr] : (r - 1) * (r + 1) = 0) with h | h
      · left; linarith
      · right; linarith
    rcases hs with rfl | rfl
    · left; ext i j
      simpa [Matrix.scalar] using (congrFun (congrFun he i) j).symm
    · right; ext i j
      by_cases hij : i = j <;>
        simpa [Matrix.scalar, coe_neg, Matrix.diagonal_apply, Matrix.one_apply, hij] using
          (congrFun (congrFun he i) j).symm
  · rintro (rfl | rfl)
    · exact (Subgroup.center _).one_mem
    · exact Subgroup.mem_center_iff.mpr (fun h => by simp)

/-- The actual projective fibers contain exactly the two matrix signs. -/
theorem realSL2_projective_eq_iff (a b : SL(2, ℝ)) :
    (QuotientGroup.mk a : PSL(2, ℝ)) = QuotientGroup.mk b ↔ a = b ∨ a = -b := by
  rw [QuotientGroup.eq, realSL2_center_eq_signs]
  constructor
  · rintro (he | he)
    · exact Or.inl (inv_mul_eq_one.mp he)
    · right
      have hb : b = a * (a⁻¹ * b) := by group
      rw [he, mul_neg, mul_one] at hb
      rw [hb, neg_neg]
  · rintro (rfl | he)
    · simp
    · have hb : b = -a := by rw [he, neg_neg]
      rw [hb, mul_neg, inv_mul_cancel]
      exact Or.inr rfl

/-- The actual central sign subgroup is compact. -/
theorem realSL2_center_isCompact : IsCompact (Subgroup.center SL(2, ℝ) : Set SL(2, ℝ)) := by
  have he : (Subgroup.center SL(2, ℝ) : Set SL(2, ℝ)) = {1, -1} := by
    ext g
    simp only [SetLike.mem_coe, realSL2_center_eq_signs, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [he]
  exact ((Set.finite_singleton _).insert _).isCompact

instance realSL2_center_isClosed : IsClosed (Subgroup.center SL(2, ℝ) : Set SL(2, ℝ)) :=
  realSL2_center_isCompact.isClosed

instance realProjectiveMeasurableSpace : MeasurableSpace PSL(2, ℝ) := borel _

instance realProjective_borelSpace : BorelSpace PSL(2, ℝ) := ⟨rfl⟩

/-- The genuine central quotient map is proper; no infinite-fiber measure collapse occurs. -/
theorem realProjectivize_isProperMap :
    IsProperMap (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨QuotientGroup.continuous_mk, QuotientGroup.isClosedMap_coe realSL2_center_isCompact, ?_⟩
  intro q
  induction q using Quotient.inductionOn with | h g => ?_
  have he : (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) ⁻¹' {QuotientGroup.mk g} = {g, -g} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_singleton_iff, realSL2_projective_eq_iff,
      Set.mem_insert_iff]
  rw [he]
  exact ((Set.finite_singleton _).insert _).isCompact

/-- Haar measure on the actual projective group is the pushforward of the original real measure. -/
def realProjectiveMeasure : Measure PSL(2, ℝ) :=
  Measure.map (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) realGroupMeasure

instance realProjectiveMeasure_isHaarMeasure : realProjectiveMeasure.IsHaarMeasure := by
  exact Measure.isHaarMeasure_map realGroupMeasure (QuotientGroup.mk' _)
    QuotientGroup.continuous_mk QuotientGroup.mk_surjective
    (isProperMap_iff_tendsto_cocompact.mp realProjectivize_isProperMap).2

/-- The actual central projection preserves the constructed measures. -/
theorem realProjectivize_measurePreserving :
    MeasurePreserving (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ))
      realGroupMeasure realProjectiveMeasure :=
  ⟨QuotientGroup.continuous_mk.measurable, rfl⟩

/-- Every genuine projective right translation preserves the pushed measure. -/
theorem realProjectiveMeasure_right_invariant (q : PSL(2, ℝ)) :
    MeasurePreserving (fun t : PSL(2, ℝ) => t * q) realProjectiveMeasure realProjectiveMeasure := by
  induction q using Quotient.inductionOn with | h g => ?_
  refine ⟨(continuous_id.mul continuous_const).measurable, ?_⟩
  have h := realProjectivize_measurePreserving.comp (realGroupMeasure_right_invariant g)
  rw [realProjectiveMeasure, Measure.map_map (by fun_prop)
    QuotientGroup.continuous_mk.measurable]
  convert h.map_eq using 1

instance realProjectiveMeasure_isMulRightInvariant : realProjectiveMeasure.IsMulRightInvariant :=
  ⟨fun q => (realProjectiveMeasure_right_invariant q).map_eq⟩

end
end Dubon2026

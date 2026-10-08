import Dubon2026.HaarInvolution
import Dubon2026.AdelicProjectiveL2Embedding

/-! # The actual rational reflection acts as a Haar-preserving real projective automorphism -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup MeasureTheory
open scoped MatrixGroups

/-- Conjugation by the actual real rational reflection negates the original two off-diagonal entries. -/
def realSL2Reflection (g : SL(2, ℝ)) : SL(2, ℝ) :=
  ⟨!![g 0 0, -g 0 1; -g 1 0, g 1 1], by
    have hg := g.property
    rw [Matrix.det_fin_two] at hg
    simpa [Matrix.det_fin_two] using hg⟩

/-- The literal reflection of the original determinant-one matrix is involutive. -/
theorem realSL2Reflection_involutive : Function.Involutive realSL2Reflection := by
  intro g
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realSL2Reflection]

/-- Literal real reflection preserves the actual matrix product. -/
theorem realSL2Reflection_mul (g h : SL(2, ℝ)) :
    realSL2Reflection (g * h) = realSL2Reflection g * realSL2Reflection h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSL2Reflection, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The original real reflection fixes the identity matrix. -/
theorem realSL2Reflection_one : realSL2Reflection 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realSL2Reflection]

/-- The actual reflection is a homomorphism of the original real special-linear group. -/
def realSL2ReflectionHom : SL(2, ℝ) →* SL(2, ℝ) where
  toFun := realSL2Reflection
  map_one' := realSL2Reflection_one
  map_mul' := realSL2Reflection_mul

/-- The literal entrywise reflection is continuous in the actual matrix topology. -/
theorem realSL2Reflection_continuous : Continuous realSL2Reflection := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    fun_prop [realSL2Reflection]

/-- Reflection of every original real matrix has exactly the genuine rational conjugation formula. -/
theorem realSL2Reflection_toGL (g : SL(2, ℝ)) :
    toGL (realSL2Reflection g) = rationalGL2ToReal rationalGL2Reflection * toGL g *
      rationalGL2ToReal rationalGL2Reflection := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSL2Reflection, rationalGL2ToReal, rationalGL2Reflection,
      GeneralLinearGroup.map, gl2UnitFirstDiagonal, toGL, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual real reflection descends through the original two-sign central quotient. -/
def realProjectiveReflectionHom : PSL(2, ℝ) →* PSL(2, ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℝ))
    ((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp realSL2ReflectionHom) (by
      intro g hg
      change (QuotientGroup.mk (realSL2Reflection g) : PSL(2, ℝ)) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [realSL2_center_eq_signs]
      rcases (realSL2_center_eq_signs g).mp hg with rfl | rfl
      · exact Or.inl realSL2Reflection_one
      · right
        ext i j
        fin_cases i <;> fin_cases j <;> simp [realSL2Reflection, coe_neg])

/-- The genuine projective reflection is involutive on every original projective class. -/
theorem realProjectiveReflectionHom_involutive : Function.Involutive realProjectiveReflectionHom := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change (QuotientGroup.mk (realSL2Reflection (realSL2Reflection g)) : PSL(2, ℝ)) = QuotientGroup.mk g
  rw [realSL2Reflection_involutive]

/-- The actual projective reflection is continuous in the genuine quotient topology. -/
theorem realProjectiveReflectionHom_continuous : Continuous realProjectiveReflectionHom :=
  (QuotientGroup.continuous_mk.comp realSL2Reflection_continuous).quotient_lift _

/-- The original reflection defines its actual involutive continuous projective group automorphism. -/
def realProjectiveReflection : PSL(2, ℝ) ≃ₜ* PSL(2, ℝ) where
  toFun := realProjectiveReflectionHom
  invFun := realProjectiveReflectionHom
  left_inv := realProjectiveReflectionHom_involutive
  right_inv := realProjectiveReflectionHom_involutive
  map_mul' := realProjectiveReflectionHom.map_mul
  continuous_toFun := realProjectiveReflectionHom_continuous
  continuous_invFun := realProjectiveReflectionHom_continuous

/-- The genuine original real projective Haar measure is preserved by the actual rational reflection. -/
theorem realProjectiveReflection_measurePreserving :
    MeasurePreserving realProjectiveReflection realProjectiveMeasure realProjectiveMeasure :=
  continuousMulEquiv_involutive_measurePreserving realProjectiveMeasure realProjectiveReflection
    realProjectiveReflectionHom_involutive

end
end Dubon2026

import Dubon2026.RealProjectiveReflection

/-! # Actual rational reflection commutes with positive real normalization -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The original rational reflection has square equal to the original identity matrix. -/
theorem rationalGL2Reflection_mul_self : rationalGL2Reflection * rationalGL2Reflection = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalGL2Reflection, gl2UnitFirstDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual real conjugation by the original rational reflection preserves positive determinant. -/
def realPositiveReflection (g : GL(2, ℝ)⁺) : GL(2, ℝ)⁺ :=
  ⟨rationalGL2ToReal rationalGL2Reflection * g.val * rationalGL2ToReal rationalGL2Reflection, by
    change 0 < (GeneralLinearGroup.det
      (rationalGL2ToReal rationalGL2Reflection * g.val * rationalGL2ToReal rationalGL2Reflection)).val
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, rationalGL2Reflection_real_det]
    simpa only [neg_one_mul, mul_neg_one, neg_neg] using g.property⟩

/-- The actual positive determinant root is unchanged by the original reflection conjugation. -/
theorem realPositiveDetRoot_reflection (g : GL(2, ℝ)⁺) :
    realPositiveDetRoot (realPositiveReflection g) = realPositiveDetRoot g := by
  unfold realPositiveDetRoot
  congr 1
  change (GeneralLinearGroup.det (rationalGL2ToReal rationalGL2Reflection * g.val *
    rationalGL2ToReal rationalGL2Reflection)).val = (GeneralLinearGroup.det g.val).val
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, rationalGL2Reflection_real_det]
  ring

/-- Genuine determinant-root normalization intertwines the original positive reflection and the actual real special-linear reflection. -/
theorem realPositiveNormalize_reflection (g : GL(2, ℝ)⁺) :
    realPositiveNormalize (realPositiveReflection g) = realSL2Reflection (realPositiveNormalize g) := by
  apply Subtype.ext
  rw [realPositiveNormalize_val, realPositiveDetRoot_reflection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realPositiveReflection, realSL2Reflection, realPositiveNormalize_val,
      rationalGL2ToReal, rationalGL2Reflection, GeneralLinearGroup.map, gl2UnitFirstDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The original rational conjugation by reflection preserves the actual positive rational subgroup. -/
def rationalPositiveReflection (g : GL(2, ℚ)⁺) : GL(2, ℚ)⁺ :=
  ⟨rationalGL2Reflection * g.val * rationalGL2Reflection, by
    change 0 < (GeneralLinearGroup.det (rationalGL2Reflection * g.val * rationalGL2Reflection)).val
    rw [map_mul, map_mul, rationalGL2Reflection, gl2UnitFirstDiagonal_det]
    simpa only [Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul, mul_neg_one, neg_neg] using g.property⟩

/-- The actual real embedding commutes with the original rational reflection conjugation. -/
theorem rationalPositiveReflection_real (g : GL(2, ℚ)⁺) :
    rationalPositiveGL2ToReal (rationalPositiveReflection g) =
      realPositiveReflection (rationalPositiveGL2ToReal g) := by
  apply Subtype.ext
  change rationalGL2ToReal (rationalGL2Reflection * g.val * rationalGL2Reflection) = _
  rw [map_mul, map_mul]
  rfl

/-- The actual finite embedding commutes with the original rational reflection conjugation. -/
theorem rationalPositiveReflection_finite (g : GL(2, ℚ)⁺) :
    rationalPositiveGL2ToFinite (rationalPositiveReflection g) =
      rationalGL2ToFinite rationalGL2Reflection * rationalPositiveGL2ToFinite g *
        rationalGL2ToFinite rationalGL2Reflection := by
  change rationalGL2ToFinite (rationalGL2Reflection * g.val * rationalGL2Reflection) = _
  rw [map_mul, map_mul]
  rfl

end
end Dubon2026

import Dubon2026.AdelicRealFiniteCommute
import Dubon2026.RealRotationGroup

/-! # Exact reversal of the original real rotation by the actual determinant-negative reflection -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The genuine determinant-negative real reflection reverses every original real rotation. -/
theorem realGL2Reflection_rotation (t : ℝ) :
    toGL (realRotationCurve t) * rationalGL2ToReal rationalGL2Reflection =
      rationalGL2ToReal rationalGL2Reflection * toGL (realRotationCurve (-t)) := by
  have he : rationalGL2ToReal rationalGL2Reflection = gl2UnitFirstDiagonal (-1 : ℝˣ) := by
    rw [rationalGL2ToReal, rationalGL2Reflection, gl2UnitFirstDiagonal_map]
    congr 1
    apply Units.ext
    norm_num
  rw [he]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realRotationCurve, gl2UnitFirstDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- The original real reflection and rotation relation holds literally in the full actual adelic group. -/
theorem adelicRealReflection_rotation (t : ℝ) :
    adelicRealSL2Embedding (realRotationCurve t) *
      adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection) =
    adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection) *
      adelicRealSL2Embedding (realRotationCurve (-t)) := by
  simpa only [map_mul, adelicRealGL2Embedding_toGL] using
    congrArg adelicRealGL2Embedding (realGL2Reflection_rotation t)

end
end Dubon2026

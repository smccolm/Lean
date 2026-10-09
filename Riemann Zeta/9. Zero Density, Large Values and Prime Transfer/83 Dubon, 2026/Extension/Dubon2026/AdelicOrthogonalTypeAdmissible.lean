import Dubon2026.AdelicRealTypeMultiplicity
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Full orthogonal compact-type admissibility of the original adelic representation -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain CongruenceSubgroup
open scoped MatrixGroups

/-- The genuine full real orthogonal group embeds as its actual invertible matrices. -/
def realOrthogonalGL2Embedding : Matrix.orthogonalGroup (Fin 2) ℝ →* Matrix.GeneralLinearGroup (Fin 2) ℝ :=
  Unitary.toUnits

/-- The actual rotation matrix is an element of the full orthogonal group, including its correct original sign convention. -/
def realOrthogonalRotation (t : ℝ) : Matrix.orthogonalGroup (Fin 2) ℝ :=
  ⟨(realRotationCurve t).val, by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realRotationCurve, Matrix.mul_apply, Fin.sum_univ_two] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]⟩

/-- The orthogonal rotation embedding is exactly the original special-linear rotation in real general-linear coordinates. -/
theorem realOrthogonalGL2Embedding_rotation (t : ℝ) :
    realOrthogonalGL2Embedding (realOrthogonalRotation t) = toGL (realRotationCurve t) :=
  Units.ext rfl

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every finite-dimensional type of the full original real orthogonal group has finite multiplicity at every original open finite adelic level. -/
theorem adelicOrthogonalType_admissible (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : Representation ℂ (Matrix.orthogonalGroup (Fin 2) ℝ) V) :
    FiniteDimensional ℂ (Representation.IntertwiningMap σ
      ((adelicFiniteFixedRealRepresentation f J).comp realOrthogonalGL2Embedding)) :=
  adelicRealType_finiteMultiplicity f hf hk J hJ realOrthogonalGL2Embedding
    (realOrthogonalRotation (Real.pi * Real.sqrt 2))
    (realOrthogonalGL2Embedding_rotation _) σ

end
end Dubon2026

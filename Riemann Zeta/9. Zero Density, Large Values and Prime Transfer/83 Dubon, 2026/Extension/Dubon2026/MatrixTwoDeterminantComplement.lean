import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # The actual determinant-complement operator detects a nonidentity residual matrix -/

namespace Dubon2026
open Matrix

variable {R K ι : Type*} [CommRing R] [Field K]

/-- For an actual invertible two-dimensional matrix, the determinant-complement operator vanishes only at the identity. -/
theorem matrixTwo_detComplement_ne_zero (A : GeneralLinearGroup (Fin 2) R) (hA : A ≠ 1) :
    A.val - (GeneralLinearGroup.det A : R) • (1 : Matrix (Fin 2) (Fin 2) R) ≠ 0 := by
  intro h
  have he : A.val = (GeneralLinearGroup.det A : R) • (1 : Matrix (Fin 2) (Fin 2) R) :=
    sub_eq_zero.mp h
  have hd : (GeneralLinearGroup.det A : R) =
      (GeneralLinearGroup.det A : R) * (GeneralLinearGroup.det A : R) := by
    change A.val.det = _
    rw [he]
    simp [Matrix.det_fin_two, pow_two]
  have hone : (GeneralLinearGroup.det A : R) = 1 := by
    apply Eq.symm
    apply (GeneralLinearGroup.det A).isUnit.mul_right_inj.mp
    simpa only [mul_one] using hd
  apply hA
  apply Units.ext
  simpa only [hone, one_smul] using he

/-- A matrix nonzero in the genuine field residue has an actual unit entry over the original local coefficient ring. -/
theorem matrix_exists_unit_entry_of_residue (r : R →+* K) [IsLocalHom r]
    (A : Matrix ι ι R) (hA : A.map r ≠ 0) : ∃ i j, IsUnit (A i j) := by
  classical
  by_contra h
  apply hA
  ext i j
  change r (A i j) = 0
  by_contra hij
  exact h ⟨i, j, isUnit_of_map_unit r _ (isUnit_iff_ne_zero.mpr hij)⟩

end Dubon2026

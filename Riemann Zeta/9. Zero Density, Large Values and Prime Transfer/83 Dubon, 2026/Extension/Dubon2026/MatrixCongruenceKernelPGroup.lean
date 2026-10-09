import Dubon2026.MatrixPrimePowerCongruence
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.PGroup

/-! # The actual prime-power group of original congruence matrices -/

namespace Dubon2026

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The literal kernel of reducing the original matrix group modulo its actual coefficient ideal. -/
abbrev MatrixCongruenceKernel (I : Ideal R) :=
  (GeneralLinearGroup.map (n := ι) (R := R) (S := R ⧸ I) (Ideal.Quotient.mk I)).ker

/-- Every original matrix in the genuine reduction kernel has its difference from one in the literal coefficient matrix ideal. -/
theorem matrixCongruenceKernel_coefficients (I : Ideal R) (u : MatrixCongruenceKernel (ι := ι) I) :
    u.val.val - 1 ∈ I.matrix ι := by
  intro i j
  have h := congrArg (fun v : GeneralLinearGroup ι (R ⧸ I) => v.val i j) u.property
  change Ideal.Quotient.mk I (u.val.val i j) = (1 : Matrix ι ι (R ⧸ I)) i j at h
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk I (u.val.val i j - (1 : Matrix ι ι R) i j) = 0
  rw [map_sub, h]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- A nilpotent original coefficient ideal containing the residue prime has an actual p-group as its matrix reduction kernel. -/
theorem matrixCongruenceKernel_isPGroup (I : Ideal R) {p N : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I) (hI : I ^ N = ⊥) :
    IsPGroup p (MatrixCongruenceKernel (ι := ι) I) := by
  intro u
  refine ⟨N, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change u.val.val ^ (p ^ N) = 1
  exact matrix_primePower_eq_one_of_nilpotent I hp hpI hI u.val.val
    (matrixCongruenceKernel_coefficients I u)

end Dubon2026

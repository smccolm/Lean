import Dubon2026.FullMatrixTracePairing
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # Genuine matrix-basis coordinates preserve original coefficient ideals -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- If all entries of an original matrix belong to a coefficient ideal, every coordinate in any genuine basis of the full matrix algebra belongs to that same ideal. -/
theorem matrixBasisCoordinate_mem_ideal (I : Ideal R)
    (b : Basis κ R (Matrix ι ι R)) (X : Matrix ι ι R)
    (hX : ∀ i j, X i j ∈ I) (k : κ) : b.repr X k ∈ I := by
  let D : Matrix ι ι R := fullMatrixTraceDuality.symm (b.coord k)
  have hd : fullMatrixTracePairing D = b.coord k :=
    fullMatrixTraceDuality.apply_symm_apply (b.coord k)
  have heval : b.repr X k = Matrix.trace (D * X) :=
    (DFunLike.congr_fun hd X).symm
  rw [heval]
  change (∑ i, ∑ j, D i j * X j i) ∈ I
  exact I.sum_mem fun i _ => I.sum_mem fun j _ => I.mul_mem_left (D i j) (hX j i)

/-- The original entrywise coefficient-ideal condition is equivalent to membership of every genuine coordinate in that same ideal. -/
theorem matrixBasisCoordinates_mem_ideal_iff [Fintype κ]
    (I : Ideal R) (b : Basis κ R (Matrix ι ι R)) (X : Matrix ι ι R) :
    (∀ i j, X i j ∈ I) ↔ ∀ k, b.repr X k ∈ I := by
  classical
  constructor
  · exact fun h k => matrixBasisCoordinate_mem_ideal I b X h k
  · intro h i j
    have he := congrArg (fun Z : Matrix ι ι R => Z i j) (b.sum_repr X)
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at he
    rw [← he]
    exact I.sum_mem fun k _ => I.mul_mem_right (b k i j) (h k)

end
end Dubon2026

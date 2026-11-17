import Dubon2026.SourceOriginalDistinctEigenbasis
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! DUB-17/18 -> original regular-prime invariant dimensions. Turn the
proved original eigenbasis into an actual original invertible conjugator;
the native diagonal trace-zero calculation can then be reused literally. -/
namespace Dubon2026
noncomputable section
open Matrix Module

/-- An original eigenbasis constructs an original matrix conjugator. -/
theorem matrix_exists_original_diagonal_conjugator_of_eigenbasis
    {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) (w : ι → F) (b : Basis ι F (ι → F))
    (hb : ∀ i, M.mulVec (b i) = w i • b i) :
    ∃ C : GeneralLinearGroup ι F,
      C.val * M * (C⁻¹).val = Matrix.diagonal w := by
  let e := Pi.basisFun F ι
  let B : GeneralLinearGroup ι F :=
    ⟨e.toMatrix b, b.toMatrix e,
      e.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip e⟩
  have hB : B.val = fun i j => b j i := by
    ext i j
    simp [B, e, Basis.toMatrix_apply]
  have hMB : M * B.val = B.val * Matrix.diagonal w := by
    ext i j
    rw [hB, Matrix.mul_diagonal]
    change (∑ k, M i k * b j k) = b j i * w j
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm]
      using congrFun (hb j) i
  refine ⟨B⁻¹, ?_⟩
  change (B⁻¹).val * M * B.val = Matrix.diagonal w
  rw [mul_assoc, hMB, ← mul_assoc, Units.inv_mul, one_mul]

/-- Distinct original characteristic roots give diagonalization entirely
over the original field, without an assumed splitting conjugator. -/
theorem matrix_exists_original_diagonal_conjugator_of_distinct_roots
    {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) (w : ι → F) (hw : Function.Injective w)
    (hroot : ∀ i, M.charpoly.IsRoot (w i)) :
    ∃ C : GeneralLinearGroup ι F,
      C.val * M * (C⁻¹).val = Matrix.diagonal w := by
  obtain ⟨b, hb⟩ := matrix_exists_original_eigenbasis_of_distinct_roots M w hw hroot
  exact matrix_exists_original_diagonal_conjugator_of_eigenbasis M w b hb

end
end Dubon2026

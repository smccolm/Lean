import Dubon2026.CMMatrixComplexEmbedding

/-! # The actual CM unitary group of a specified Hermitian form

The DUB-17 source chooses a definite unitary form with specified finite
local behavior. Keeping that form as a matrix retains its arithmetic
content; it is not silently replaced by the identity matrix.
-/

namespace Dubon2026

noncomputable section

open NumberField

variable {K ι : Type*} [Field K] [NumberField K] [IsCMField K]
variable [Fintype ι] [DecidableEq ι]

/-- The original invertible CM matrices preserving the specified sesquilinear form. -/
def cmHermitianUnitaryGroup (H : Matrix ι ι K) : Subgroup (Matrix ι ι K)ˣ where
  carrier := {M | star M.val * H * M.val = H}
  one_mem' := by simp
  mul_mem' {A B} ha hb := by
    change star (A.val * B.val) * H * (A.val * B.val) = H
    rw [star_mul]
    calc
      _ = star B.val * (star A.val * H * A.val) * B.val := by simp only [mul_assoc]
      _ = H := by rw [ha, hb]
  inv_mem' {M} hM := by
    change star (M⁻¹).val * H * (M⁻¹).val = H
    calc
      _ = star (M⁻¹).val * (star M.val * H * M.val) * (M⁻¹).val := by rw [hM]
      _ = star (M.val * (M⁻¹).val) * H * (M.val * (M⁻¹).val) := by
        simp only [star_mul, mul_assoc]
      _ = H := by simp

/-- A complex embedding carries a preserving CM matrix to an isometry of the original embedded form. -/
theorem cmHermitianUnitaryGroup_complex_preserves (H : Matrix ι ι K)
    (M : cmHermitianUnitaryGroup H) (φ : K →+* ℂ) :
    star (φ.mapMatrix M.val.val) * φ.mapMatrix H * φ.mapMatrix M.val.val = φ.mapMatrix H := by
  have h := congrArg (cmMatrixComplexEmbedding φ) M.property
  simpa only [map_mul, map_star] using h

end
end Dubon2026

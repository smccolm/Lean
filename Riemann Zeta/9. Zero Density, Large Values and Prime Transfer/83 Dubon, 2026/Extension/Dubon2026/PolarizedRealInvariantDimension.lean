import Dubon2026.SkewTransposeCoordinates
import Dubon2026.PolarizedAdjointRepresentation
import Dubon2026.PolarizedInvolution

/-! CHT Lemma 2.1.3 for the actual odd real-place polarization: the
fixed full adjoint is the skew-transpose space after multiplication by
the original symmetric matrix. Its exact dimension is required in the
DUB-17 source polarized Selmer comparison. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {n : ℕ} {K : Type} [Field K] (B : GeneralLinearGroup (Fin n) K)

/-- The full adjoint action at the actual original symmetric polarization element. -/
theorem polarizedAdjointRepresentation_involution (X : Matrix (Fin n) (Fin n) K) :
    polarizedAdjointRepresentation (polarizedInvolution B) X = B.val * (-Xᵀ) * B.inv := by
  rw [polarizedAdjointRepresentation_apply]
  change B.val * polarizedAdjointRepresentation polarizedComplexConjugation X * B.inv = _
  rw [polarizedAdjointRepresentation_j]

/-- The original odd real-place full-adjoint fixed space. -/
def polarizedRealInvariants : Submodule K (Matrix (Fin n) (Fin n) K) :=
  (polarizedAdjointRepresentation (polarizedInvolution B) - LinearMap.id).ker

/-- Original real invariance is exactly skew transpose after multiplication by the actual polarization matrix. -/
theorem polarizedRealInvariants_iff (hB : B.valᵀ = B.val)
    (X : Matrix (Fin n) (Fin n) K) :
    X ∈ polarizedRealInvariants B ↔ X * B.val ∈ skewTransposeMatrices n K := by
  change polarizedAdjointRepresentation (polarizedInvolution B) X - X = 0 ↔
    (X * B.val)ᵀ + X * B.val = 0
  rw [sub_eq_zero, polarizedAdjointRepresentation_involution, Matrix.transpose_mul, hB]
  constructor
  · intro h
    have hc := congrArg (fun M : Matrix (Fin n) (Fin n) K => M * B.val) h
    simp only [Matrix.mul_assoc, B.inv_val, Matrix.mul_one] at hc
    rw [← hc, Matrix.mul_neg, add_neg_cancel]
  · intro h
    have he : B.val * (-Xᵀ) = X * B.val := by
      rw [Matrix.mul_neg]
      exact neg_eq_of_add_eq_zero_left (by simpa only [add_comm] using h)
    rw [he, Matrix.mul_assoc, B.val_inv, Matrix.mul_one]

/-- The actual original real fixed space is linearly equivalent to the same-size skew-transpose matrices. -/
def polarizedRealInvariantSkewEquiv (hB : B.valᵀ = B.val) :
    polarizedRealInvariants B ≃ₗ[K] skewTransposeMatrices n K where
  toFun X := ⟨X.val * B.val, (polarizedRealInvariants_iff B hB X.val).mp X.property⟩
  invFun Y := ⟨Y.val * B.inv, (polarizedRealInvariants_iff B hB _).mpr (by
    simpa only [Matrix.mul_assoc, B.inv_val, Matrix.mul_one] using Y.property)⟩
  left_inv X := Subtype.ext (by simp only [Matrix.mul_assoc, B.val_inv, Matrix.mul_one])
  right_inv Y := Subtype.ext (by simp only [Matrix.mul_assoc, B.inv_val, Matrix.mul_one])
  map_add' X Y := Subtype.ext (add_mul X.val Y.val B.val)
  map_smul' a X := Subtype.ext (smul_mul_assoc a X.val B.val)

/-- The original odd real-place full-adjoint invariant dimension is the exact source triangular term. -/
theorem polarizedRealInvariants_finrank (hB : B.valᵀ = B.val) (h2 : (2 : K) ≠ 0) :
    Module.finrank K (polarizedRealInvariants B) = n * (n - 1) / 2 :=
  (polarizedRealInvariantSkewEquiv B hB).finrank_eq.trans (skewTransposeMatrices_finrank n K h2)

end
end Dubon2026

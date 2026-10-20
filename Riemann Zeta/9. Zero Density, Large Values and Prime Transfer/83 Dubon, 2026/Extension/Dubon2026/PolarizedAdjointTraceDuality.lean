import Dubon2026.PolarizedAdjointRepresentation
import Dubon2026.FullMatrixTracePairing
import Mathlib.RepresentationTheory.Intertwining

/-! The actual polarized full adjoint is self-dual for the original trace
pairing. This is the coefficient duality in the source polarized Selmer
comparison required for DUB-17, including its disconnected component. -/

namespace Dubon2026
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Literal conjugation preserves the full trace pairing. -/
theorem matrixTracePairing_conjugate (g : GeneralLinearGroup ι R)
    (X Y : Matrix ι ι R) :
    Matrix.trace ((g.val * X * g.inv) * (g.val * Y * g.inv)) = Matrix.trace (X * Y) := by
  have h : (g.val * X * g.inv) * (g.val * Y * g.inv) = g.val * (X * Y) * g.inv := by
    simp only [mul_assoc, ← mul_assoc g.inv g.val, g.inv_val, one_mul]
  rw [h, Matrix.trace_mul_comm]
  simp only [← mul_assoc, g.inv_val, one_mul]

omit [DecidableEq ι] in
/-- Negative transpose preserves the same full trace pairing. -/
theorem matrixTracePairing_negTranspose (X Y : Matrix ι ι R) :
    Matrix.trace ((-X.transpose) * (-Y.transpose)) = Matrix.trace (X * Y) := by
  rw [neg_mul_neg, ← transpose_mul, trace_transpose, trace_mul_comm]

/-- The full disconnected source group preserves the actual trace pairing. -/
theorem polarizedAdjoint_tracePairing (g : PolarizedGaloisGroup ι R)
    (X Y : Matrix ι ι R) :
    Matrix.trace (polarizedAdjointRepresentation g X * polarizedAdjointRepresentation g Y) =
      Matrix.trace (X * Y) := by
  have hc (z : Multiplicative (ZMod 2)) :
      Matrix.trace (polarizedAdjointRepresentation (SemidirectProduct.inr z) X *
        polarizedAdjointRepresentation (SemidirectProduct.inr z) Y) = Matrix.trace (X * Y) := by
    by_cases hz : z = 1
    · subst z
      simp
    · have hz' : z = Multiplicative.ofAdd (1 : ZMod 2) := by
        apply Multiplicative.toAdd.injective
        have h0 : z.toAdd ≠ 0 := fun h => hz (Multiplicative.toAdd.injective h)
        generalize z.toAdd = x at h0 ⊢
        fin_cases x
        · exact (h0 rfl).elim
        · rfl
      subst z
      change Matrix.trace (polarizedAdjointRepresentation polarizedComplexConjugation X *
        polarizedAdjointRepresentation polarizedComplexConjugation Y) = _
      rw [polarizedAdjointRepresentation_j, polarizedAdjointRepresentation_j]
      exact matrixTracePairing_negTranspose X Y
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  simp only [map_mul, Module.End.mul_apply]
  change Matrix.trace (polarizedAdjointRepresentation (polarizedIdentityComponent g.left)
      (polarizedAdjointRepresentation (SemidirectProduct.inr g.right) X) *
    polarizedAdjointRepresentation (polarizedIdentityComponent g.left)
      (polarizedAdjointRepresentation (SemidirectProduct.inr g.right) Y)) = _
  rw [polarizedAdjointRepresentation_identity, polarizedAdjointRepresentation_identity,
    matrixTracePairing_conjugate]
  exact hc g.right

/-- The source adjoint intertwines the genuine full trace pairing with its linear dual. -/
theorem polarizedAdjoint_traceIntertwining (g : PolarizedGaloisGroup ι R)
    (X : Matrix ι ι R) :
    fullMatrixTracePairing (polarizedAdjointRepresentation g X) =
      polarizedAdjointRepresentation.dual g (fullMatrixTracePairing X) := by
  ext Y
  change Matrix.trace (polarizedAdjointRepresentation g X * Y) =
    Matrix.trace (X * polarizedAdjointRepresentation g⁻¹ Y)
  have h := polarizedAdjoint_tracePairing g X (polarizedAdjointRepresentation g⁻¹ Y)
  have he : polarizedAdjointRepresentation g (polarizedAdjointRepresentation g⁻¹ Y) = Y := by
    change (polarizedAdjointRepresentation g * polarizedAdjointRepresentation g⁻¹) Y = Y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rwa [he] at h

/-- The original full matrix trace duality is an equivalence of polarized adjoint representations. -/
noncomputable def polarizedAdjointTraceDuality :
    Representation.Equiv (polarizedAdjointRepresentation (ι := ι) (R := R))
      polarizedAdjointRepresentation.dual where
  toLinearEquiv := fullMatrixTraceDuality
  isIntertwining' g := by
    apply LinearMap.ext
    intro X
    exact polarizedAdjoint_traceIntertwining g X

end Dubon2026

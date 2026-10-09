import Dubon2026.AdelicReflectedWeightProjection
import Dubon2026.AdelicRaisingHilbertBasis

/-! # The original raising vectors and their real reflections with exact signed weights -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The exact integer weights of the actual raising and reflected raising vectors. -/
def adelicSignedRaisingWeight (k : ℤ) : ℕ ⊕ ℕ → ℤ :=
  Sum.elim (fun n => k + 2 * (n : ℤ)) (fun n => -(k + 2 * (n : ℤ)))

/-- Positive original weight makes all signed raising weights pairwise distinct. -/
theorem adelicSignedRaisingWeight_injective (k : ℤ) (hk : 0 < k) :
    Function.Injective (adelicSignedRaisingWeight k) := by
  intro a b he
  cases a <;> cases b <;>
    simp only [adelicSignedRaisingWeight, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at he ⊢ <;> omega

/-- Each genuine signed integer rotation character has unit modulus. -/
theorem integerIrrationalCharacter_norm (m : ℤ) : ‖integerIrrationalCharacter m‖ = 1 := by
  rw [integerIrrationalCharacter, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual positive raising family and its actual negative real reflection in the original Hilbert space. -/
def adelicSignedRaisingJet : ℕ ⊕ ℕ → AdelicCyclicHilbert f :=
  Sum.elim (fun n => (adelicRaisingJet f n).val)
    (fun n => adelicCyclicHilbertRepresentation f
      (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection)) (adelicRaisingJet f n).val)

/-- Every original signed raising vector transforms by its exact integer character at every real rotation angle. -/
theorem adelicSignedRaisingJet_rotation_all (hf : f ≠ 0) (i : ℕ ⊕ ℕ) (t : ℝ) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t))
      (adelicSignedRaisingJet f i) =
      Complex.exp ((t : ℂ) * (Complex.I * (adelicSignedRaisingWeight k i : ℂ))) •
        adelicSignedRaisingJet f i := by
  cases i with
  | inl n =>
    simpa only [adelicSignedRaisingJet, adelicSignedRaisingWeight, Sum.elim_inl,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using
      adelicRaisingJet_rotation f hf n t
  | inr n =>
    simpa only [adelicSignedRaisingJet, adelicSignedRaisingWeight, Sum.elim_inr,
      Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Complex.ofReal_neg, neg_mul, mul_neg] using adelicReflectedRaisingJet_rotation f hf n t

/-- The original signed raising family has precisely its genuine integer irrational-angle eigenvalues. -/
theorem adelicSignedRaisingJet_rotation (hf : f ≠ 0) (i : ℕ ⊕ ℕ) :
    adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))) (adelicSignedRaisingJet f i) =
      integerIrrationalCharacter (adelicSignedRaisingWeight k i) • adelicSignedRaisingJet f i := by
  cases i with
  | inl n =>
    have he := adelicRaisingJet_rotation f hf n (Real.pi * Real.sqrt 2)
    change adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))) (adelicRaisingJet f n).val =
      irrationalRotationCharacter k n • (adelicRaisingJet f n).val at he
    rw [irrationalRotationCharacter_integer] at he
    exact he
  | inr n =>
    have he := adelicReflectedRaisingJet_rotation f hf n (Real.pi * Real.sqrt 2)
    rw [irrationalRotationCharacter_negative] at he
    exact he

/-- Every original signed raising vector is nonzero, including each actual unitary reflection. -/
theorem adelicSignedRaisingJet_ne_zero (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    adelicSignedRaisingJet f i ≠ 0 := by
  cases i with
  | inl n => exact adelicRaisingJet_val_ne_zero f hf hk n
  | inr n =>
    intro he
    have hn : ‖(adelicRaisingJet f n).val‖ = 0 :=
      (adelicCyclicHilbertOperator_norm f
        (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection)) (adelicRaisingJet f n).val).symm.trans
        ((congrArg norm he).trans norm_zero)
    exact adelicRaisingJet_val_ne_zero f hf hk n (norm_eq_zero.mp hn)

/-- Distinct original signed raising vectors are orthogonal for the original Hilbert inner product. -/
theorem adelicSignedRaisingJet_orthogonal (hf : f ≠ 0) (hk : 0 < k) :
    Pairwise (fun i j => inner ℂ (adelicSignedRaisingJet f i) (adelicSignedRaisingJet f j) = 0) := by
  intro i j hij
  exact @unitary_distinct_eigen_inner_zero (AdelicCyclicHilbert f) inferInstance inferInstance
    (adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))))
    (adelicCyclicHilbertRepresentation_inner f _) _ _ _ _
    (integerIrrationalCharacter_norm _)
    (integerIrrationalCharacter_injective.ne ((adelicSignedRaisingWeight_injective k hk).ne hij))
    (adelicSignedRaisingJet_rotation f hf i) (adelicSignedRaisingJet_rotation f hf j)

/-- The original signed raising family normalized by its actual original Hilbert norm. -/
def adelicNormalizedSignedRaisingJet (i : ℕ ⊕ ℕ) : AdelicCyclicHilbert f :=
  ((‖adelicSignedRaisingJet f i‖⁻¹ : ℝ) : ℂ) • adelicSignedRaisingJet f i

/-- Actual normalization gives a genuine orthonormal family across both real determinant components. -/
theorem adelicNormalizedSignedRaisingJet_orthonormal (hf : f ≠ 0) (hk : 0 < k) :
    Orthonormal ℂ (adelicNormalizedSignedRaisingJet f) :=
  @normalizedOrthogonal_orthonormal (AdelicCyclicHilbert f) (ℕ ⊕ ℕ) inferInstance inferInstance
    (adelicSignedRaisingJet f) (adelicSignedRaisingJet_ne_zero f hf hk)
    (adelicSignedRaisingJet_orthogonal f hf hk)

end
end Dubon2026

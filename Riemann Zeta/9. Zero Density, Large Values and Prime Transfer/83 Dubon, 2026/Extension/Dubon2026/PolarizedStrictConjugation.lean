import Dubon2026.PolarizedStrictKernel
import Dubon2026.PolarizedAdjointRepresentation

/-! Conjugation on the actual fixed-similitude infinitesimal kernel is
exactly the source full adjoint action. This is the necessary comparison
between the polarized deformation fiber and cohomology for DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Actual identity-component conjugation on the infinitesimal kernel is reduced matrix conjugation. -/
theorem polarizedStrictPoint_identityConjugate
    (x : GeneralLinearGroup ι (DualNumber R) × (DualNumber R)ˣ) (X : Matrix ι ι R) :
    polarizedIdentityComponent (R := DualNumber R) (ι := ι) x * polarizedStrictPoint X *
      (polarizedIdentityComponent (R := DualNumber R) (ι := ι) x)⁻¹ =
      polarizedStrictPoint ((dualMatrixReduction x.1).val * X * (dualMatrixReduction x.1).inv) := by
  change polarizedIdentityComponent (R := DualNumber R) (ι := ι) x *
    polarizedIdentityComponent (R := DualNumber R) (ι := ι) (dualMatrixStrictUnit X, 1) *
    (polarizedIdentityComponent (R := DualNumber R) (ι := ι) x)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (polarizedIdentityComponent (R := DualNumber R) (ι := ι))
  apply Prod.ext
  · exact dualMatrixStrictUnit_conjugate x.1 X
  · change x.2 * 1 * x.2⁻¹ = 1
    simp

/-- The source disconnected involution acts on the actual strict kernel by negative transpose. -/
theorem polarizedStrictPoint_jConjugate (X : Matrix ι ι R) :
    polarizedComplexConjugation (R := DualNumber R) (ι := ι) * polarizedStrictPoint X *
      (polarizedComplexConjugation (R := DualNumber R) (ι := ι))⁻¹ =
      polarizedStrictPoint (-X.transpose) := by
  change polarizedComplexConjugation (R := DualNumber R) (ι := ι) *
    polarizedIdentityComponent (R := DualNumber R) (ι := ι) (dualMatrixStrictUnit X, 1) *
    (polarizedComplexConjugation (R := DualNumber R) (ι := ι))⁻¹ = _
  rw [polarizedComplexConjugation_conjugate]
  apply congrArg (polarizedIdentityComponent (R := DualNumber R) (ι := ι))
  apply Prod.ext
  · change GeneralLinearGroup.scalar ι 1 *
      polarizedContragredient (ι := ι) (R := DualNumber R) (dualMatrixStrictUnit X) = _
    rw [map_one, one_mul, dualMatrixStrictUnit_contragredient]
    rfl
  · rfl

/-- The source component subgroup has the same actual infinitesimal and adjoint action. -/
theorem polarizedStrictPoint_componentConjugate (z : Multiplicative (ZMod 2))
    (X : Matrix ι ι R) :
      (SemidirectProduct.inr z : PolarizedGaloisGroup ι (DualNumber R)) *
        polarizedStrictPoint X * (SemidirectProduct.inr z)⁻¹ =
      polarizedStrictPoint (polarizedAdjointRepresentation (R := R) (ι := ι)
        (SemidirectProduct.inr z) X) := by
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
      change polarizedComplexConjugation (R := DualNumber R) (ι := ι) * polarizedStrictPoint X *
        (polarizedComplexConjugation (R := DualNumber R) (ι := ι))⁻¹ =
        polarizedStrictPoint (polarizedAdjointRepresentation (R := R) (ι := ι)
          (polarizedComplexConjugation (R := R) (ι := ι)) X)
      rw [polarizedAdjointRepresentation_j]
      exact polarizedStrictPoint_jConjugate X

/-- The whole actual dual-number polarized group acts on its strict kernel through the reduced full adjoint. -/
theorem polarizedStrictPoint_conjugate (g : PolarizedGaloisGroup ι (DualNumber R))
    (X : Matrix ι ι R) :
    g * polarizedStrictPoint X * g⁻¹ =
      polarizedStrictPoint (polarizedAdjointRepresentation (R := R) (ι := ι)
        (polarizedDualReduction g) X) := by
  calc
    g * polarizedStrictPoint X * g⁻¹ =
        polarizedIdentityComponent (R := DualNumber R) (ι := ι) g.left *
          ((SemidirectProduct.inr g.right) * polarizedStrictPoint X *
            (SemidirectProduct.inr g.right)⁻¹) *
              (polarizedIdentityComponent (R := DualNumber R) (ι := ι) g.left)⁻¹ := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
      simp only [_root_.mul_inv_rev, mul_assoc, polarizedIdentityComponent]
    _ = polarizedStrictPoint ((dualMatrixReduction g.left.1).val *
        polarizedAdjointRepresentation (R := R) (ι := ι) (SemidirectProduct.inr g.right) X *
          (dualMatrixReduction g.left.1).inv) := by
      rw [polarizedStrictPoint_componentConjugate, polarizedStrictPoint_identityConjugate]
    _ = _ := by
      conv_rhs => rw [polarizedAdjointRepresentation_apply]
      rfl

end
end Dubon2026

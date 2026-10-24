import Dubon2026.SourceEllipticAbscissaVariableCoefficients

/-! Intrinsic finite-kernel quotient models respect the original coordinate
change. The native curve coefficients and the already proved Velu scaling
give literal model equality. This is required to transfer the composite
cyclic-root bijection to the original elliptic curves in the inertia census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticVariableChange
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
variable (C : VariableChange F) (W : WeierstrassCurve F) (S : Finset F)

/-- The intrinsic odd quotient transforms as the original Weierstrass curve. -/
theorem variableChange_abscissaQuotient :
    abscissaQuotient (C • W) (S.image (vcXInv C)) = C • abscissaQuotient W S := by
  have hinj : Function.Injective (vcXInv C) :=
    (show Function.LeftInverse (vcX C) (vcXInv C) from fun x => vcX_vcXInv x).injective
  have hT : ∑ x ∈ S.image (vcXInv C), abscissaVeluT (C • W) x =
      ((C.u⁻¹ : Fˣ) : F) ^ 4 * ∑ x ∈ S, abscissaVeluT W x := by
    rw [Finset.sum_image hinj.injOn, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => variableChange_abscissaVeluT C W x
  have hW : ∑ x ∈ S.image (vcXInv C), abscissaVeluW (C • W) x =
      ((C.u⁻¹ : Fˣ) : F) ^ 6 *
        ((∑ x ∈ S, abscissaVeluW W x) - C.r * ∑ x ∈ S, abscissaVeluT W x) := by
    rw [Finset.sum_image hinj.injOn, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => variableChange_abscissaVeluW C W x
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  ext
  · simp only [abscissaQuotient, variableChange_a₁]
  · simp only [abscissaQuotient, variableChange_a₂]
  · simp only [abscissaQuotient, variableChange_a₃]
  · simp only [abscissaQuotient, variableChange_a₄, hT, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp only [abscissaQuotient, variableChange_a₆, hT, hW, b₂,
      variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
    field_simp
    ring

/-- The actual degree-two coefficient model transforms under the same coordinate change. -/
theorem variableChange_twoAbscissaQuotient (h2 : (2 : F) ≠ 0) :
    twoAbscissaQuotient (C • W) (S.image (vcXInv C)) =
      C • twoAbscissaQuotient W S := by
  have hinj : Function.Injective (vcXInv C) :=
    (show Function.LeftInverse (vcX C) (vcXInv C) from fun x => vcX_vcXInv x).injective
  have hT : ∑ x ∈ S.image (vcXInv C), twoAbscissaG (C • W) x =
      ((C.u⁻¹ : Fˣ) : F) ^ 4 * ∑ x ∈ S, twoAbscissaG W x := by
    rw [Finset.sum_image hinj.injOn, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => variableChange_twoAbscissaG C W h2 x
  have hW : ∑ x ∈ S.image (vcXInv C), x * twoAbscissaG (C • W) x =
      ((C.u⁻¹ : Fˣ) : F) ^ 6 *
        ((∑ x ∈ S, x * twoAbscissaG W x) - C.r * ∑ x ∈ S, twoAbscissaG W x) := by
    rw [Finset.sum_image hinj.injOn, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [variableChange_twoAbscissaG C W h2, vcXInv]
    ring
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  ext
  · simp only [twoAbscissaQuotient, variableChange_a₁]
  · simp only [twoAbscissaQuotient, variableChange_a₂]
  · simp only [twoAbscissaQuotient, variableChange_a₃]
  · simp only [twoAbscissaQuotient, variableChange_a₄, hT, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp only [twoAbscissaQuotient, variableChange_a₆, hT, hW, b₂,
      variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
    field_simp
    ring

end
end Dubon2026.SourceEllipticVelu

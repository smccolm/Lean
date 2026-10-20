import Dubon2026.PolarizedGaloisGroupLaws

/-! A symmetric original polarization matrix gives the odd real-place
involution in the source target. This is the matrix construction needed
to extend the CM residual representation in DUB-17. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The original symmetric polarization matrix determines the source real-place element. -/
def polarizedInvolution (B : GeneralLinearGroup ι R) : PolarizedGaloisGroup ι R :=
  ⟨(B, 1), Multiplicative.ofAdd (1 : ZMod 2)⟩

/-- A symmetric original matrix has contragredient equal to its inverse. -/
theorem polarizedContragredient_eq_inv_of_symmetric (B : GeneralLinearGroup ι R)
    (hB : B.val.transpose = B.val) : polarizedContragredient B = B⁻¹ := by
  apply mul_left_cancel (a := B)
  rw [mul_inv_cancel]
  apply Units.ext
  change B.val * B.inv.transpose = 1
  rw [← hB, ← Matrix.transpose_mul, B.inv_val, Matrix.transpose_one]

/-- The original symmetric polarization gives an element of order dividing two. -/
theorem polarizedInvolution_sq (B : GeneralLinearGroup ι R)
    (hB : B.val.transpose = B.val) : polarizedInvolution B ^ 2 = 1 := by
  rw [pow_two]
  apply SemidirectProduct.ext
  · change (B, (1 : Rˣ)) * polarizedSwitchAction (Multiplicative.ofAdd (1 : ZMod 2)) (B, 1) = 1
    rw [polarizedSwitchAction_generator]
    apply Prod.ext
    · change B * (GeneralLinearGroup.scalar ι 1 * polarizedContragredient B) = 1
      rw [map_one, one_mul, polarizedContragredient_eq_inv_of_symmetric B hB, mul_inv_cancel]
    · exact one_mul 1
  · change Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1
    decide

/-- The original real-place element belongs to the nonidentity component. -/
theorem polarizedInvolution_component (B : GeneralLinearGroup ι R) :
    polarizedComponent (polarizedInvolution B) = Multiplicative.ofAdd (1 : ZMod 2) := rfl

/-- The constructed real-place element has the required odd source similitude. -/
theorem polarizedInvolution_similitude (B : GeneralLinearGroup ι R) :
    polarizedSimilitude (polarizedInvolution B) = -1 := by
  simp [polarizedSimilitude, polarizedInvolution, polarizedComponentSign]

end Dubon2026

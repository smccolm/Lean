import Dubon2026.PolarizedContragredient

/-! The exact involution defining CHT Section 2.1's disconnected polarized
group. The multiplier is preserved, while the original matrix is sent to its
multiplier times inverse transpose. This serves the CM deformation comparison
needed for DUB-17; it does not construct a modular Galois representation. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Original scalar matrices commute with every invertible matrix. -/
theorem polarizedScalar_commute (u : Rˣ) (g : GeneralLinearGroup ι R) :
    Commute (GeneralLinearGroup.scalar ι u) g := by
  apply Units.ext
  exact Matrix.scalar_commute (u : R) (Commute.all _) g.val

/-- The literal CHT involution on the identity component. -/
def polarizedSwitch (x : GeneralLinearGroup ι R × Rˣ) : GeneralLinearGroup ι R × Rˣ :=
  (GeneralLinearGroup.scalar ι x.2 * polarizedContragredient x.1, x.2)

/-- Preservation of products follows from centrality of the multiplier. -/
theorem polarizedSwitch_mul (x y : GeneralLinearGroup ι R × Rˣ) :
    polarizedSwitch (x * y) = polarizedSwitch x * polarizedSwitch y := by
  apply Prod.ext
  · change GeneralLinearGroup.scalar ι (x.2 * y.2) * polarizedContragredient (x.1 * y.1) =
      (GeneralLinearGroup.scalar ι x.2 * polarizedContragredient x.1) *
        (GeneralLinearGroup.scalar ι y.2 * polarizedContragredient y.1)
    rw [map_mul, map_mul]
    have hc := polarizedScalar_commute y.2 (polarizedContragredient x.1)
    calc
      _ = GeneralLinearGroup.scalar ι x.2 *
          (GeneralLinearGroup.scalar ι y.2 * polarizedContragredient x.1) *
            polarizedContragredient y.1 := by simp only [mul_assoc]
      _ = _ := by rw [hc.eq]; simp only [mul_assoc]
  · rfl

/-- The multiplier and inverse transpose cancel on the second application. -/
theorem polarizedSwitch_involutive :
    Function.Involutive (polarizedSwitch (R := R) (ι := ι)) := by
  intro x
  apply Prod.ext
  · change GeneralLinearGroup.scalar ι x.2 *
      polarizedContragredient (GeneralLinearGroup.scalar ι x.2 * polarizedContragredient x.1) = x.1
    rw [map_mul, polarizedContragredient_scalar]
    have hi : polarizedContragredient (polarizedContragredient x.1) = x.1 :=
      polarizedInverseTranspose_involutive x.1
    rw [hi, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · rfl

/-- The exact multiplier-preserving automorphism used for the semidirect product. -/
def polarizedSwitchAut : MulAut (GeneralLinearGroup ι R × Rˣ) where
  toFun := polarizedSwitch
  invFun := polarizedSwitch
  left_inv := polarizedSwitch_involutive
  right_inv := polarizedSwitch_involutive
  map_mul' := polarizedSwitch_mul

/-- The switching automorphism squares to the identity. -/
theorem polarizedSwitchAut_sq : (polarizedSwitchAut (R := R) (ι := ι)) ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  exact polarizedSwitch_involutive x

end Dubon2026

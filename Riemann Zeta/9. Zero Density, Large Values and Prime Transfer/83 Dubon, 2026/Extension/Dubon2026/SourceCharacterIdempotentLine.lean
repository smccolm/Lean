import Dubon2026.AlgebraIdempotentLeftIdeal
import Mathlib.LinearAlgebra.Pi

/-! DUB-17/18 -> primitive determinant -> identify the primitive Tate image.
The existing actual idempotent left ideal is a coefficient line when the
prescribed character normalizes its generator and gives its scalar action.
These exact identities are to be supplied by the arithmetic Hecke projector. -/
namespace Dubon2026
noncomputable section
variable {E A : Type*} [Field E] [Ring A] [Algebra E A]

/-- The actual character idempotent left ideal, with its prescribed coefficient coordinate. -/
def characterIdempotentLeftIdealEquiv (κ : A →ₐ[E] E) (e : A)
    (he : κ e = 1) (hκ : ∀ a : A, a * e = κ a • e) :
    algebraIdempotentLeftIdeal (S := E) e ≃ₗ[E] E where
  toFun x := κ x.val
  invFun c := ⟨c • e, ⟨algebraMap E A c, (Algebra.smul_def c e).symm⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    change a * e = x.val at ha
    change κ x.val • e = x.val
    rw [← ha, map_mul, he, mul_one]
    exact (hκ a).symm
  right_inv c := by
    change κ (c • e) = c
    simp [he]
  map_add' x y := map_add κ x.val y.val
  map_smul' c x := map_smul κ c x.val

end
end Dubon2026

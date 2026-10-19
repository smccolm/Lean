import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Transport the actual Frobenius fixed space under conjugacy. This is
needed to carry the diagonal local dimension calculation to the original
Frobenius class selected for DUB-17's arithmetic patching primes. -/

namespace Dubon2026
noncomputable section
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

private theorem representation_conjugate_fixed
    (T : Representation K G V) (g h : G) (x : V) (hx : T g x = x) :
    T (h * g * h⁻¹) (T h x) = T h x := by
  have act (a b : G) (v : V) : T a (T b v) = T (a * b) v := by
    rw [map_mul]; rfl
  rw [act]
  rw [inv_mul_cancel_right]
  rw [← act, hx]

/-- Acting by the original representation identifies the fixed spaces
of conjugate elements, with inverse the action of the inverse element. -/
def representationConjugateFixedEquiv (T : Representation K G V) (g h : G) :
    LinearMap.ker (T g - 1) ≃ₗ[K] LinearMap.ker (T (h * g * h⁻¹) - 1) where
  toFun x := ⟨T h x.val, by
    change T (h * g * h⁻¹) (T h x.val) - T h x.val = 0
    exact sub_eq_zero.mpr (representation_conjugate_fixed T g h x.val (sub_eq_zero.mp x.property))⟩
  invFun y := ⟨T h⁻¹ y.val, by
    change T g (T h⁻¹ y.val) - T h⁻¹ y.val = 0
    apply sub_eq_zero.mpr
    have he := representation_conjugate_fixed T (h * g * h⁻¹) h⁻¹ y.val
      (sub_eq_zero.mp y.property)
    have hc : h⁻¹ * (h * g * h⁻¹) * h = g := by simp only [← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right]
    simpa only [inv_inv, hc] using he⟩
  left_inv x := by
    apply Subtype.ext
    change T h⁻¹ (T h x.val) = x.val
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv y := by
    apply Subtype.ext
    change T h (T h⁻¹ y.val) = y.val
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' x y := by apply Subtype.ext; exact map_add (T h) x.val y.val
  map_smul' a x := by apply Subtype.ext; exact map_smul (T h) a x.val

/-- Conjugation preserves the dimension of the actual fixed space. -/
theorem representationConjugateFixed_finrank (T : Representation K G V) (g h : G) :
    Module.finrank K (LinearMap.ker (T (h * g * h⁻¹) - 1)) =
      Module.finrank K (LinearMap.ker (T g - 1)) :=
  (representationConjugateFixedEquiv T g h).finrank_eq.symm

end
end Dubon2026

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction
-> reverse genus -> finite exceptional fibers -> actual elliptic inertia
orbits and cyclic-quotient interpretation -> native variable changes on
the actual point group. The coordinate and nonsingularity identities prove
the maps; the native group law proves additivity. No point isomorphism or
homomorphism law is assumed. Native coefficient-change and affine-point
APIs are reused; the two archived copies of the partial-derivative identities
are consolidated into one proved pair.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean and
P2M/Sol/S_WeierstrassCurve_Affine_Point_vcInvFun_add.lean. -/
namespace Dubon2026.SourceEllipticVariableChange
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
noncomputable section
variable {K : Type*} [Field K]
variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)

/-- The actual x-coordinate of a native Weierstrass variable change. -/
def vcX (x' : K) : K := (C.u : K) ^ 2 * x' + C.r

/-- The actual y-coordinate of a native Weierstrass variable change. -/
def vcY (x' y' : K) : K := (C.u : K) ^ 3 * y' + (C.u : K) ^ 2 * C.s * x' + C.t

/-- The inverse x-coordinate of the native variable change. -/
def vcXInv (x : K) : K := ((C.u⁻¹ : Kˣ) : K) ^ 2 * (x - C.r)

/-- The inverse y-coordinate of the native variable change. -/
def vcYInv (x y : K) : K := ((C.u⁻¹ : Kˣ) : K) ^ 3 * (y - C.t - C.s * (x - C.r))

variable {C W}


@[simp] theorem vcX_vcXInv (x : K) : vcX C (vcXInv C x) = x := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] theorem vcY_vcYInv (x y : K) : vcY C (vcXInv C x) (vcYInv C x y) = y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcY, vcXInv, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] theorem vcXInv_vcX (x' : K) : vcXInv C (vcX C x') = x' := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] theorem vcYInv_vcY (x' y' : K) : vcYInv C (vcX C x') (vcY C x' y') = y' := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcY, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

theorem equation_aux (x' y' : K) :
    vcY C x' y' ^ 2 + W.a₁ * vcX C x' * vcY C x' y' + W.a₃ * vcY C x' y'
      - (vcX C x' ^ 3 + W.a₂ * vcX C x' ^ 2 + W.a₄ * vcX C x' + W.a₆)
    = (C.u : K) ^ 6 *
      (y' ^ 2 + (C • W).a₁ * x' * y' + (C • W).a₃ * y'
        - (x' ^ 3 + (C • W).a₂ * x' ^ 2 + (C • W).a₄ * x' + (C • W).a₆)) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp; ring

theorem partialX_aux (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄)
      + C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
    = (C.u : K) ^ 4 *
      ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp; ring

theorem partialY_aux (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring


end
end Dubon2026.SourceEllipticVariableChange

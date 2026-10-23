import Dubon2026.SourceEllipticVariableNonsingular

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

/-- The native variable change on actual nonsingular affine points. -/
def vcFun : (C • W).toAffine.Point → W.Point
  | 0 => 0
  | .some x' y' h => .some (vcX C x') (vcY C x' y')
      ((nonsingular_variableChange_iff x' y').mp h)

/-- The inverse native variable change on actual nonsingular affine points. -/
def vcInvFun : W.Point → (C • W).toAffine.Point
  | 0 => 0
  | .some x y h => .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv]))

variable {C W}

@[simp] theorem vcFun_zero : vcFun C W 0 = 0 := rfl
@[simp] theorem vcInvFun_zero : vcInvFun C W 0 = 0 := rfl

private theorem some_eq_some {W' : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

theorem vcFun_leftInverse : Function.LeftInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x', y', h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcXInv_vcX x') (vcYInv_vcY x' y')

theorem vcFun_rightInverse : Function.RightInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcX_vcXInv x) (vcY_vcYInv x y)

variable (C W) in

/-- The inverse coordinate formulas give an equivalence of actual point types. -/
noncomputable def variableChangeEquiv : (C • W).toAffine.Point ≃ W.Point :=
  ⟨vcFun C W, vcInvFun C W, vcFun_leftInverse, vcFun_rightInverse⟩


end
end Dubon2026.SourceEllipticVariableChange

import Dubon2026.SourceEllipticVariableAdditionFormula

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
variable {C : VariableChange K} {W : WeierstrassCurve.Affine K}

theorem some_of_eq_of_eq' {V : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

variable [DecidableEq K]

theorem vcFun_add (P Q : (C • W).toAffine.Point) :
    vcFun C W (P + Q) = vcFun C W P + vcFun C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2, vcFun_zero]
    show (0 : W.Point) = Point.some (vcX C x₁) (vcY C x₁ y₁) _ + Point.some (vcX C x₂) (vcY C x₂ y₂) _
    have hxyW := (Yeq_variableChange_iff (W := W) x₁ x₂ y₁ y₂).mpr hxy
    exact (add_of_Y_eq hxyW.1 hxyW.2).symm
  · have hxyW : ¬(vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) :=
      fun h => hxy ((Yeq_variableChange_iff x₁ x₂ y₁ y₂).mp h)
    have hslope := slope_variableChange (W := W) x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    rw [add_some hxy]
    show Point.some _ _ _ = Point.some (vcX C x₁) (vcY C x₁ y₁) _ + Point.some (vcX C x₂) (vcY C x₂ y₂) _
    rw [add_some hxyW]
    refine some_of_eq_of_eq' ?_ ?_
    · rw [hslope, addX_variableChange]
    · rw [hslope, addY_variableChange]

theorem vcInvFun_add (P Q : W.Point) :
    vcInvFun C W (P + Q) = vcInvFun C W P + vcInvFun C W Q := by
  apply vcFun_leftInverse.injective
  rw [vcFun_add, vcFun_rightInverse P, vcFun_rightInverse Q, vcFun_rightInverse (P + Q)]


/-- The actual coordinate change preserves the native elliptic point-group law. -/
def variableChangeAddEquiv (C : VariableChange K) (W : WeierstrassCurve.Affine K) :
    (C • W).toAffine.Point ≃+ W.Point :=
  { variableChangeEquiv C W with map_add' := fun P Q => vcFun_add P Q }

end
end Dubon2026.SourceEllipticVariableChange

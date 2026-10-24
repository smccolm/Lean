import Dubon2026.SourceEllipticVariableAddEquiv

/-! The literal elliptic negation is a coordinate change stabilizing the
actual curve. Its point action is native group negation. This supplies the
sign in the source full-inertia-image statement for the DUB-17/18 cyclic
orbit and exceptional-fiber comparison.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_equivariant_torsion_reduction_ofJ, Coord section.
Only the required characteristic-not-two nonidentity argument is used. -/
namespace Dubon2026.SourceEllipticStabilizer
open WeierstrassCurve SourceEllipticVariableChange
noncomputable section
variable {K : Type*} [Field K]

/-- The coordinate change giving the actual elliptic group negation. -/
def negationChange (W : WeierstrassCurve K) : VariableChange K :=
  ⟨-1, 0, -W.a₁, -W.a₃⟩

theorem negationChange_smul (W : WeierstrassCurve K) : negationChange W • W = W := by
  ext <;> simp [negationChange, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆] <;> ring

theorem negationChange_ne_one (W : WeierstrassCurve K) (h2 : (2 : K) ≠ 0) :
    negationChange W ≠ 1 := by
  intro h
  have hu := congrArg (fun C : VariableChange K => (C.u : K)) h
  have hneg : (-1 : K) = 1 := by simpa only [negationChange, VariableChange.one_def,
    Units.val_neg, Units.val_one] using hu
  apply h2
  linear_combination -hneg

theorem vcXInv_negationChange (W : WeierstrassCurve K) (x : K) :
    vcXInv (negationChange W) x = x := by
  simp [vcXInv, negationChange]

theorem vcYInv_negationChange (W : WeierstrassCurve K) (x y : K) :
    vcYInv (negationChange W) x y = W.toAffine.negY x y := by
  simp only [vcYInv, negationChange, Affine.negY, inv_neg, inv_one, Units.val_neg, Units.val_one]
  simp
  ring

private theorem zero_heq_of_curve_eq {V W : WeierstrassCurve.Affine K} (h : V = W) :
    HEq (Affine.Point.zero : V.Point) (Affine.Point.zero : W.Point) := by
  subst W
  rfl

private theorem some_heq_of_curve_eq {V W : WeierstrassCurve.Affine K}
    (h : V = W) {x y x' y' : K} (hx : x = x') (hy : y = y')
    {hP : V.Nonsingular x y} {hQ : W.Nonsingular x' y'} :
    HEq (Affine.Point.some x y hP) (Affine.Point.some x' y' hQ) := by
  subst W
  subst x'
  subst y'
  rfl

theorem vcInvFun_negationChange_heq (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    HEq (vcInvFun (negationChange W) W.toAffine P) (-P) := by
  cases P with
  | zero => exact zero_heq_of_curve_eq (negationChange_smul W)
  | some x y h =>
    change HEq (Affine.Point.some _ _ _) (-Affine.Point.some x y h)
    rw [Affine.Point.neg_some]
    exact some_heq_of_curve_eq (negationChange_smul W)
      (vcXInv_negationChange W x) (vcYInv_negationChange W x y)

end
end Dubon2026.SourceEllipticStabilizer

import Dubon2026.SourceEllipticVariableCoordinates

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

theorem equation_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Equation x' y' ↔ W.Equation (vcX C x') (vcY C x' y') := by
  rw [equation_iff', equation_iff', equation_aux x' y', mul_eq_zero,
    or_iff_right (pow_ne_zero 6 C.u.ne_zero)]

private theorem partials_zero_iff (x' y' : K) :
    ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄) = 0
        ∧ 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0)
      ↔ (W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄) = 0
        ∧ 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0) := by
  constructor
  · rintro ⟨hX', hY'⟩
    have hY : 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0 := by
      rw [partialY_aux x' y', hY', mul_zero]
    refine ⟨?_, hY⟩
    have hX := partialX_aux (C := C) (W := W) x' y'
    rw [hX', mul_zero, hY, mul_zero, add_zero] at hX
    exact hX
  · rintro ⟨hX, hY⟩
    have hY' : 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0 := by
      have h := partialY_aux (C := C) (W := W) x' y'
      rw [hY] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 3 C.u.ne_zero)
    refine ⟨?_, hY'⟩
    have h := partialX_aux (C := C) (W := W) x' y'
    rw [hX, hY, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 4 C.u.ne_zero)

theorem nonsingular_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Nonsingular x' y' ↔ W.Nonsingular (vcX C x') (vcY C x' y') := by
  rw [nonsingular_iff', nonsingular_iff', equation_variableChange_iff x' y']
  refine and_congr_right fun _ => not_iff_not.mp ?_
  push Not
  exact partials_zero_iff x' y'


end
end Dubon2026.SourceEllipticVariableChange

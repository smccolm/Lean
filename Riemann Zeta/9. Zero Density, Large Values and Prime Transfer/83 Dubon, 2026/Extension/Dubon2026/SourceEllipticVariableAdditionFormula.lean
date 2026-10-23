import Dubon2026.SourceEllipticVariablePointEquiv

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

theorem vcX_injective : Function.Injective (vcX C) := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX] at h
  have : (C.u : K) ^ 2 * a = (C.u : K) ^ 2 * b := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 2 hu) this

theorem vcY_injective (x' : K) : Function.Injective (vcY C x') := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcY] at h
  have : (C.u : K) ^ 3 * a = (C.u : K) ^ 3 * b := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 3 hu) this

theorem negY_variableChange (x' y' : K) :
    W.negY (vcX C x') (vcY C x' y') = vcY C x' ((C • W).toAffine.negY x' y') := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem Yeq_variableChange_iff (x₁' x₂' y₁' y₂' : K) :
    (vcX C x₁' = vcX C x₂' ∧ vcY C x₁' y₁' = W.negY (vcX C x₂') (vcY C x₂' y₂'))
      ↔ (x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂') := by
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : x₁' = x₂' := vcX_injective hx
    subst hx'
    refine ⟨rfl, ?_⟩
    rw [negY_variableChange x₁' y₂'] at hy
    exact vcY_injective x₁' hy
  · rintro ⟨hx, hy⟩
    subst hx
    exact ⟨rfl, by rw [negY_variableChange x₁' y₂', hy]⟩

theorem slope_variableChange [DecidableEq K] (x₁' x₂' y₁' y₂' : K)
    (h₁ : (C • W).toAffine.Equation x₁' y₁') (h₂ : (C • W).toAffine.Equation x₂' y₂')
    (hxy : ¬(x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂')) :
    W.slope (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') (vcY C x₂' y₂')
      = (C.u : K) * (C • W).toAffine.slope x₁' x₂' y₁' y₂' + C.s := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  by_cases hx : x₁' = x₂'
  · have hy : y₁' ≠ (C • W).toAffine.negY x₂' y₂' := fun h => hxy ⟨hx, h⟩
    have hyy : y₁' = y₂' := (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    subst hx
    subst hyy
    have hyW : vcY C x₁' y₁' ≠ W.negY (vcX C x₁') (vcY C x₁' y₁') := by
      intro h
      exact hy ((Yeq_variableChange_iff x₁' x₁' y₁' y₁').mp ⟨rfl, h⟩).2
    rw [slope_of_Y_ne rfl hyW, slope_of_Y_ne rfl hy]
    have hd : vcY C x₁' y₁' - W.negY (vcX C x₁') (vcY C x₁' y₁')
        = (C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁') := by
      rw [negY_variableChange x₁' y₁']
      simp only [vcY]
      ring
    have hPYden : y₁' - (C • W).toAffine.negY x₁' y₁'
        = 2 * y₁' + (C • W).a₁ * x₁' + (C • W).a₃ := by
      simp only [negY]
      ring
    have hn : 3 * vcX C x₁' ^ 2 + 2 * W.a₂ * vcX C x₁' + W.a₄ - W.a₁ * vcY C x₁' y₁'
        = (C.u : K) ^ 4 * (3 * x₁' ^ 2 + 2 * (C • W).a₂ * x₁'
            + (C • W).a₄ - (C • W).a₁ * y₁')
          + C.s * ((C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁')) := by
      have hX := partialX_aux (C := C) (W := W) x₁' y₁'
      have hY := partialY_aux (C := C) (W := W) x₁' y₁'
      rw [hPYden]
      linear_combination (-1 : K) * hX + C.s * hY
    have hden' : y₁' - (C • W).toAffine.negY x₁' y₁' ≠ 0 := sub_ne_zero_of_ne hy
    rw [hd, hn]
    field_simp
  · have hxW : vcX C x₁' ≠ vcX C x₂' := fun h => hx (vcX_injective h)
    rw [slope_of_X_ne hxW, slope_of_X_ne hx]
    have hd : vcX C x₁' - vcX C x₂' = (C.u : K) ^ 2 * (x₁' - x₂') := by
      simp only [vcX]; ring
    have hn : vcY C x₁' y₁' - vcY C x₂' y₂'
        = (C.u : K) ^ 3 * (y₁' - y₂') + (C.u : K) ^ 2 * C.s * (x₁' - x₂') := by
      simp only [vcY]; ring
    rw [hd, hn]
    have hxne : x₁' - x₂' ≠ 0 := sub_ne_zero_of_ne hx
    field_simp

theorem addX_variableChange (x₁' x₂' L : K) :
    W.addX (vcX C x₁') (vcX C x₂') ((C.u : K) * L + C.s)
      = vcX C ((C • W).toAffine.addX x₁' x₂' L) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [addX, vcX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem addY_variableChange (x₁' x₂' y₁' L : K) :
    W.addY (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') ((C.u : K) * L + C.s)
      = vcY C ((C • W).toAffine.addX x₁' x₂' L) ((C • W).toAffine.addY x₁' x₂' y₁' L) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [addY, negAddY, addX, negY, vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring


end
end Dubon2026.SourceEllipticVariableChange

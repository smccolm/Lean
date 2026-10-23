import Dubon2026.SourceEllipticVeluTwoPointMap

/-! The zero fiber of the actual degree-two Velu point map. This is the kernel
geometry input to the quotient group map, and hence to the cyclic-subgroup
interpretation of modular-polynomial roots used by the elliptic inertia census
for DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2. Additivity remains required.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the kernel geometry in
S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] {W : WeierstrassCurve F} {x₀ y₀ : F}

theorem negY_eq_of_veluGy_eq_zero (hgy : veluGy W x₀ y₀ = 0) :
    W.toAffine.negY x₀ y₀ = y₀ := by
  simp only [veluGy] at hgy
  simp only [WeierstrassCurve.Affine.negY]
  linear_combination hgy

theorem eq_of_equation_of_veluGy_eq_zero (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) {y : F} (h : W.toAffine.Equation x₀ y) : y = y₀ := by
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h hQ rfl with hy | hy
  · exact hy
  · rw [hy, negY_eq_of_veluGy_eq_zero hgy]

theorem some_eq_of_X_eq_of_veluGy_eq_zero (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hns : W.toAffine.Nonsingular x₀ y₀)
    {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = x₀) :
    WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some x₀ y₀ hns := by
  have hy := eq_of_equation_of_veluGy_eq_zero hQ hgy (hx ▸ h.left)
  subst hx
  subst hy
  rfl

theorem two_nsmul_some_eq_zero_of_veluGy_eq_zero [DecidableEq F]
    (hgy : veluGy W x₀ y₀ = 0) (hns : W.toAffine.Nonsingular x₀ y₀) :
    2 • (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : W.toAffine.Point) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
    (negY_eq_of_veluGy_eq_zero hgy).symm

theorem veluPointMap2_eq_zero_iff (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0)
    (hns : W.toAffine.Nonsingular x₀ y₀) (P : W.toAffine.Point) :
    veluPointMap2 hQ hgy hΔ P = 0 ↔
      P = 0 ∨ P = WeierstrassCurve.Affine.Point.some x₀ y₀ hns := by
  cases P with
  | zero => exact iff_of_true rfl (Or.inl rfl)
  | some x y h =>
    by_cases hx : x = x₀
    · exact iff_of_true (veluPointMap2_some_of_eq hQ hgy hΔ h hx)
        (Or.inr (some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hns h hx))
    · rw [veluPointMap2_some_of_ne hQ hgy hΔ h hx]
      simp only [WeierstrassCurve.Affine.Point.some_ne_zero, false_or, false_iff,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact fun heq => hx heq.1

theorem addOrderOf_some_eq_two_of_veluGy_eq_zero [DecidableEq F]
    (hgy : veluGy W x₀ y₀ = 0) (hns : W.toAffine.Nonsingular x₀ y₀) :
    addOrderOf (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : W.toAffine.Point) = 2 :=
  addOrderOf_eq_prime (two_nsmul_some_eq_zero_of_veluGy_eq_zero hgy hns)
    (WeierstrassCurve.Affine.Point.some_ne_zero hns)

theorem veluPointMap2_eq_zero_iff_mem_zmultiples [DecidableEq F]
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
    (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0) (hns : W.toAffine.Nonsingular x₀ y₀)
    (P : W.toAffine.Point) :
    veluPointMap2 hQ hgy hΔ P = 0 ↔
      P ∈ AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some x₀ y₀ hns) := by
  classical
  have hf : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : W.toAffine.Point) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, two_nsmul_some_eq_zero_of_veluGy_eq_zero hgy hns⟩
  rw [veluPointMap2_eq_zero_iff hQ hgy hΔ hns,
    hf.mem_zmultiples_iff_mem_range_addOrderOf,
    addOrderOf_some_eq_two_of_veluGy_eq_zero hgy hns]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, zero_nsmul _⟩
    · exact ⟨1, by norm_num, one_nsmul _⟩
  · rintro ⟨n, hn, rfl⟩
    interval_cases n <;> simp

end
end Dubon2026.SourceEllipticVelu

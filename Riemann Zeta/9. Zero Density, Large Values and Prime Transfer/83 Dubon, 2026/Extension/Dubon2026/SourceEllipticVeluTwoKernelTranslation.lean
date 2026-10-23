import Dubon2026.SourceEllipticVeluTwoNegation

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation -> good
reduction -> reverse genus -> elliptic inertia census -> cyclic-quotient root
interpretation -> actual degree-two quotient group homomorphism.
This step proves negation compatibility and invariance under translation by
the kernel generator. Full additivity, including secant and tangent cases,
remains a required obligation. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

theorem veluGx_ne_zero_of_quotΔ (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0) :
    veluGx W x₀ y₀ ≠ 0 := fun h =>
  hΔ (by rw [veluQuotient2_Delta_eq hQ hgy, h]; ring)

theorem velu2_addX_kernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀)
      = x₀ + veluGx W x₀ y₀ / (x - x₀) := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  simp only [WeierstrassCurve.Affine.slope_of_X_ne hx, WeierstrassCurve.Affine.addX, veluGx]
  field_simp
  linear_combination hP - hQ - (y - y₀) * hord

omit [DecidableEq F] in

theorem velu2X_sub_velu2X {x₁ x₂ : F} (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀) :
    velu2X W x₀ y₀ x₁ - velu2X W x₀ y₀ x₂
      = (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - veluGx W x₀ y₀)
          / ((x₁ - x₀) * (x₂ - x₀)) := by
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  simp only [velu2X]
  field_simp
  ring

omit [DecidableEq F] in

theorem velu2X_eq_iff {x₁ x₂ : F} (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀) :
    velu2X W x₀ y₀ x₁ = velu2X W x₀ y₀ x₂
      ↔ x₁ = x₂ ∨ (x₁ - x₀) * (x₂ - x₀) = veluGx W x₀ y₀ := by
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  rw [← sub_eq_zero, velu2X_sub_velu2X hx₁ hx₂, div_eq_zero_iff, mul_eq_zero,
    sub_eq_zero, sub_eq_zero]
  simp only [mul_ne_zero hd₁ hd₂, or_false]

theorem velu2X_addKernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
    (ht : veluGx W x₀ y₀ ≠ 0) (hx : x ≠ x₀) :
    velu2X W x₀ y₀ (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
      = velu2X W x₀ y₀ x := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have htd : veluGx W x₀ y₀ / (x - x₀) ≠ 0 := div_ne_zero ht hd
  rw [velu2_addX_kernel hP hQ hgy hx]
  simp only [velu2X, add_sub_cancel_left]
  field_simp
  ring

theorem velu2_addY_kernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) - y₀
      = -(veluGx W x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀)) / (x - x₀) ^ 2 := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hxP := velu2_addX_kernel hP hQ hgy hx
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope_of_X_ne hx] at hxP ⊢
  rw [hxP]
  field_simp
  linear_combination -((x - x₀) ^ 2 * hord)

theorem velu2Y_addKernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
    (ht : veluGx W x₀ y₀ ≠ 0) (hx : x ≠ x₀) :
    velu2Y W x₀ y₀ (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
        (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀))
      = velu2Y W x₀ y₀ x y := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hxP := velu2_addX_kernel hP hQ hgy hx
  have hyP := velu2_addY_kernel hP hQ hgy hx
  simp only [velu2Y]
  have htd : veluGx W x₀ y₀ / (x - x₀) ≠ 0 := div_ne_zero ht hd

  rw [hxP, add_sub_cancel_left]

  have key : veluGx W x₀ y₀
        * (W.a₁ * (veluGx W x₀ y₀ / (x - x₀))
            + W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) - y₀)
        / (veluGx W x₀ y₀ / (x - x₀)) ^ 2
      = y₀ - y := by
    rw [sub_eq_iff_eq_add.mp hyP]
    field_simp
    ring
  rw [key]
  linear_combination hyP

variable (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
  (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0)

omit [DecidableEq F] in

private theorem v2ker_some_congr {W' : WeierstrassCurve.Affine F} {u₁ u₂ v₁ v₂ : F}
    {h₁ : W'.Nonsingular u₁ v₁} {h₂ : W'.Nonsingular u₂ v₂} (hX : u₁ = u₂) (hY : v₁ = v₂) :
    WeierstrassCurve.Affine.Point.some u₁ v₁ h₁ = WeierstrassCurve.Affine.Point.some u₂ v₂ h₂ := by
  subst hX; subst hY; rfl

include hQ hgy hΔ in

theorem veluPointMap2_add_kernel_gen (hQns : W.toAffine.Nonsingular x₀ y₀)
    (P : W.toAffine.Point) :
    veluPointMap2 hQ hgy hΔ (P + .some x₀ y₀ hQns)
      = veluPointMap2 hQ hgy hΔ P := by
  have ht : veluGx W x₀ y₀ ≠ 0 := veluGx_ne_zero_of_quotΔ hQ hgy hΔ

  have h2P₀ : (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = 0 :=
    two_nsmul_some_eq_zero_of_veluGy_eq_zero hgy hQns
  cases P with
  | zero =>
    rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add, WeierstrassCurve.Affine.Point.zero_def, veluPointMap2_zero]
    exact veluPointMap2_some_of_eq hQ hgy hΔ hQns rfl
  | some x y h =>
    by_cases hx : x = x₀
    ·
      have hPP₀ : WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x₀ y₀ hQns :=
        some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hx
      rw [hPP₀, ← two_nsmul, h2P₀, veluPointMap2_some_of_eq hQ hgy hΔ hQns rfl]
      rfl
    ·
      have hnsA : W.toAffine.Nonsingular
          (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
          (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)) :=
        WeierstrassCurve.Affine.nonsingular_add h hQns fun hc => hx hc.1
      have hPP₀ : WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x₀ y₀ hQns
          = WeierstrassCurve.Affine.Point.some _ _ hnsA := WeierstrassCurve.Affine.Point.add_of_X_ne hx

      have hxA : W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) ≠ x₀ := by
        rw [velu2_addX_kernel h.1 hQ hgy hx]
        simpa using div_ne_zero ht (sub_ne_zero.mpr hx)
      rw [hPP₀, veluPointMap2_some_of_ne hQ hgy hΔ hnsA hxA,
        veluPointMap2_some_of_ne hQ hgy hΔ h hx]
      exact v2ker_some_congr (velu2X_addKernel h.1 hQ hgy ht hx)
        (velu2Y_addKernel h.1 hQ hgy ht hx)

end Field


end
end Dubon2026.SourceEllipticVelu

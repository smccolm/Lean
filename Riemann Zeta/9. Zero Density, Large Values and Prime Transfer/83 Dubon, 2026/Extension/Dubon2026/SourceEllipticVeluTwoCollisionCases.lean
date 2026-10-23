import Dubon2026.SourceEllipticVeluTwoAddCases

/-! Remaining coordinate and case analysis for the actual degree-two Velu
group homomorphism. The dependency is DUB-17 / DUB-18 -> continuation -> good
reduction -> reverse genus -> elliptic inertia census -> cyclic-quotient root
interpretation -> quotient homomorphisms with their actual cyclic kernels.
Compatibility predicates in intermediate lemmas describe explicit secant and
tangent coordinate obligations; the final consumer must derive them all.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2. All source option
changes and irrelevant logical anchors are omitted. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

theorem velu2_quotNegY_sub_factored (hgy : veluGy W x₀ y₀ = 0)
    {x : F} (y : F) (hx : x ≠ x₀) :
    (x - x₀) ^ 2
        * (velu2Y W x₀ y₀ x y
            - (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y))
      = (y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - veluGx W x₀ y₀) := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2X, velu2Y, WeierstrassCurve.Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃, veluGx]
  field_simp
  linear_combination (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) * hord

variable (hgy : veluGy W x₀ y₀ = 0) (hQns : W.toAffine.Nonsingular x₀ y₀)

include hgy hQns in

theorem velu2X_ne_of_diffAvoid
    {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀) :
    velu2X W x₀ y₀ x₁ ≠ velu2X W x₀ y₀ x₂ := by
  intro hXeq
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁

  have hfib : (x₁ - x₀) * (x₂ - x₀) = veluGx W x₀ y₀ :=
    ((velu2X_eq_iff hx₁ hx₂).mp hXeq).resolve_left hx12

  have hx₂eq : x₂ = W.toAffine.addX x₁ x₀ (W.toAffine.slope x₁ x₀ y₁ y₀) := by
    rw [velu2_addX_kernel h₁.1 hQns.1 hgy hx₁]
    field_simp
    linear_combination hfib

  have hnsA : W.toAffine.Nonsingular
      (W.toAffine.addX x₁ x₀ (W.toAffine.slope x₁ x₀ y₁ y₀))
      (W.toAffine.addY x₁ x₀ y₁ (W.toAffine.slope x₁ x₀ y₁ y₀)) :=
    WeierstrassCurve.Affine.nonsingular_add h₁ hQns fun hxy => hx₁ hxy.1
  have hP1P0 : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some x₀ y₀ hQns
      = WeierstrassCurve.Affine.Point.some _ _ hnsA :=
    WeierstrassCurve.Affine.Point.add_of_X_ne hx₁

  have hnegP₀ : -(WeierstrassCurve.Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simpa only [WeierstrassCurve.Affine.Point.some.injEq] using And.intro (Eq.refl x₀) (negY_eq_of_veluGy_eq_zero hgy)

  rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := h₂) (h₂ := hnsA)).mp hx₂eq with hPeq | hPeq
  ·
    refine hsm ?_
    have hdiff : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - WeierstrassCurve.Affine.Point.some x₂ y₂ h₂
        = WeierstrassCurve.Affine.Point.some x₀ y₀ hQns := by
      rw [hPeq, ← hP1P0, sub_add_cancel_left, hnegP₀]
    rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.add_of_X_ne hx12,
      WeierstrassCurve.Affine.Point.some.injEq] at hdiff
    exact hdiff.1
  ·
    refine hsp ?_
    have hsum : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂
        = WeierstrassCurve.Affine.Point.some x₀ y₀ hQns := by
      rw [hPeq, ← hP1P0, ← sub_eq_add_neg, sub_add_cancel_left, hnegP₀]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12, WeierstrassCurve.Affine.Point.some.injEq] at hsum
    exact hsum.1

include hgy hQns in

theorem velu2Y_ne_quotNegY_of_tangent
    {x y : F} (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀) :
    velu2Y W x₀ y₀ x y
      ≠ (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y) := by
  intro hcon
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx

  have hfact : (y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - veluGx W x₀ y₀) = 0 := by
    have h0 := velu2_quotNegY_sub_factored hgy y hx
    rw [sub_eq_zero.mpr hcon, mul_zero] at h0
    exact h0.symm

  have hd2t : (x - x₀) ^ 2 = veluGx W x₀ y₀ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr hy))

  have hxPP₀ : W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) = x := by
    rw [velu2_addX_kernel h.1 hQns.1 hgy hx, ← hd2t]
    field_simp
    ring

  have hnsA : W.toAffine.Nonsingular
      (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
      (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)) :=
    WeierstrassCurve.Affine.nonsingular_add h hQns fun hxy => hx hxy.1
  have hPP₀ : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some x₀ y₀ hQns
      = WeierstrassCurve.Affine.Point.some _ _ hnsA :=
    WeierstrassCurve.Affine.Point.add_of_X_ne hx

  have hnegP₀ : -(WeierstrassCurve.Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simpa only [WeierstrassCurve.Affine.Point.some.injEq] using And.intro (Eq.refl x₀) (negY_eq_of_veluGy_eq_zero hgy)

  rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := hnsA) (h₂ := h)).mp hxPP₀ with hPeq | hPeq
  ·
    rw [← hPP₀, add_eq_left] at hPeq
    exact WeierstrassCurve.Affine.Point.some_ne_zero hQns hPeq
  ·
    refine hx2 ?_
    have h2P : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some x y h
        = WeierstrassCurve.Affine.Point.some x₀ y₀ hQns := by
      have heq := hPP₀.trans hPeq
      rw [← hnegP₀, eq_neg_iff_add_eq_zero, add_right_comm, heq, neg_add_cancel]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy, WeierstrassCurve.Affine.Point.some.injEq] at h2P
    exact h2P.1

end Field


end
end Dubon2026.SourceEllipticVelu

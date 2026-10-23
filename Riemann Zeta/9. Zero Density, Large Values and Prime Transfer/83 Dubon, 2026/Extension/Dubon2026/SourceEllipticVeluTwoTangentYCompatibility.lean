import Dubon2026.SourceEllipticVeluTwoTangentXCompatibility

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

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}

theorem velu2_tanY_negAddY_align (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
    (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : velu2Y W x₀ y₀ x y
      ≠ (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y)) :
    velu2Y W x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.negAddY x x y (W.toAffine.slope x x y y))
      = (veluQuotient2 W x₀ y₀).toAffine.negAddY (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
          (velu2Y W x₀ y₀ x y)
          ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
            (velu2Y W x₀ y₀ x y) (velu2Y W x₀ y₀ x y)) := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hD : (x - x₀) ^ 2 - veluGx W x₀ y₀ ≠ 0 := by
    intro hD0
    refine sub_ne_zero.mpr hY ?_
    have h5a := velu2_quotNegY_sub_factored hgy y hx
    rw [hD0, mul_zero] at h5a
    exact (mul_eq_zero.mp h5a).resolve_left (pow_ne_zero 2 hd)
  have hd2P : W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀ ≠ 0 := sub_ne_zero.mpr hx2
  have hsdEq : (2 * y + W.a₁ * x + W.a₃) = y - W.toAffine.negY x y := by
    simp only [WeierstrassCurve.Affine.negY]; ring
  have hSIYt := velu2_tangent_negAddY_cleared_identity hP hQ hord hy
  have hSI2c := velu2_tanY_SI2c hP hQ hord

  rw [hsdEq] at hSI2c
  have hXalign := velu2_tanX_align hP hQ hgy hy hx hx2 hY

  have hColQ :
      (velu2Y W x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
              (W.toAffine.negAddY x x y (W.toAffine.slope x x y y))
            - velu2Y W x₀ y₀ x y)
          * ((y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - veluGx W x₀ y₀))
        = ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * ((x - x₀) ^ 2 - veluGx W x₀ y₀)
              + veluGx W x₀ y₀
                * (W.a₁ ^ 2 * (x - x₀)
                    + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          * (velu2X W x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
              - velu2X W x₀ y₀ x) := by

    set x2P := W.toAffine.addX x x (W.toAffine.slope x x y y) with hx2P_def
    set nAY := W.toAffine.negAddY x x y (W.toAffine.slope x x y y) with hnAY_def

    have hx2P_rel : (x2P - x₀) * (y - W.toAffine.negY x y) ^ 2
        = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
          + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (y - W.toAffine.negY x y)
          - (W.a₂ + 2 * x + x₀) * (y - W.toAffine.negY x y) ^ 2 := by
      rw [hx2P_def]; exact velu2_tan_d2P_cleared hy
    have hnAY_rel : (y - W.toAffine.negY x y) * (nAY - y)
        = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (x2P - x) := by
      rw [hnAY_def, hx2P_def]
      simp only [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negAddY]
      field_simp; ring
    simp only [velu2X, velu2Y]
    field_simp [hd, hd2P]
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hsd) hd) ?_
    linear_combination
      (-veluGx W x₀ y₀ * ((x - x₀) ^ 2 - veluGx W x₀ y₀)
          * (y - W.toAffine.negY x y) ^ 3) * hSIYt
      + (-veluGx W x₀ y₀ * (x2P - x) * ((x - x₀) * (x2P - x₀) - veluGx W x₀ y₀)
          * (W.a₁ ^ 2 * (x - x₀)
              + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (x - x₀) ^ 2) * hx2P_rel
      + ((x - x₀) * (y - W.toAffine.negY x y) ^ 2 * ((x - x₀) ^ 2 - veluGx W x₀ y₀)
          * ((x - x₀) * (x2P - x₀) - veluGx W x₀ y₀)
          * ((x - x₀) * (x2P - x₀) + veluGx W x₀ y₀)) * hnAY_rel
      + (-veluGx W x₀ y₀ * (x2P - x) * ((x - x₀) * (x2P - x₀) - veluGx W x₀ y₀)) * hSI2c

  conv_rhs => rw [WeierstrassCurve.Affine.negAddY, ← hXalign, velu2_tan_quotSlope_eq hgy hx hy hY]
  rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add, eq_div_iff (mul_ne_zero hsd hD)]
  linear_combination hColQ

theorem velu2_tanY_align (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
    (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : velu2Y W x₀ y₀ x y
      ≠ (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y)) :
    velu2Y W x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y))
      = (veluQuotient2 W x₀ y₀).toAffine.addY (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
          (velu2Y W x₀ y₀ x y)
          ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
            (velu2Y W x₀ y₀ x y) (velu2Y W x₀ y₀ x y)) := by
  have hXalign := velu2_tanX_align hP hQ hgy hy hx hx2 hY
  have hnAY := velu2_tanY_negAddY_align hP hQ hgy hy hx hx2 hY
  rw [WeierstrassCurve.Affine.addY, velu2Y_negY hgy, WeierstrassCurve.Affine.addY, hXalign, hnAY]

end Field


end
end Dubon2026.SourceEllipticVelu

import Dubon2026.SourceEllipticVeluTwoSecantCompatibility

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

theorem velu2_tan_d2P_cleared (hy : y ≠ W.toAffine.negY x y) :
    (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) * (y - W.toAffine.negY x y) ^ 2
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
        + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (y - W.toAffine.negY x y)
        - (W.a₂ + 2 * x + x₀) * (y - W.toAffine.negY x y) ^ 2 := by
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  simp only [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, WeierstrassCurve.Affine.addX]
  field_simp
  ring

theorem velu2_tan_quotSlope_eq (hgy : veluGy W x₀ y₀ = 0)
    (hx : x ≠ x₀) (hy : y ≠ W.toAffine.negY x y)
    (hY : velu2Y W x₀ y₀ x y
      ≠ (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y)) :
    (veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
        (velu2Y W x₀ y₀ x y) (velu2Y W x₀ y₀ x y)
      = ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * ((x - x₀) ^ 2 - veluGx W x₀ y₀)
            + veluGx W x₀ y₀
              * (W.a₁ ^ 2 * (x - x₀)
                  + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          / ((y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - veluGx W x₀ y₀)) := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hsdp : velu2Y W x₀ y₀ x y
      - (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y) ≠ 0 :=
    sub_ne_zero.mpr hY

  have hD : (x - x₀) ^ 2 - veluGx W x₀ y₀ ≠ 0 := by
    intro hD0
    refine hsdp ?_
    have h5a := velu2_quotNegY_sub_factored hgy y hx
    rw [hD0, mul_zero] at h5a
    exact (mul_eq_zero.mp h5a).resolve_left (pow_ne_zero 2 hd)
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hY, div_eq_div_iff hsdp (mul_ne_zero hsd hD)]
  simp only [velu2X, velu2Y, veluQuotient2_a₁, veluQuotient2_a₂, veluQuotient2_a₃,
    veluQuotient2_a₄, WeierstrassCurve.Affine.negY, veluGx]
  field_simp
  linear_combination (-(3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
      * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
            * ((x - x₀) ^ 2 - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀))
          + (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
            * (W.a₁ ^ 2 * (x - x₀)
                + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))) * hord

theorem velu2_tanX_align (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : velu2Y W x₀ y₀ x y
      ≠ (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y)) :
    velu2X W x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
      = (veluQuotient2 W x₀ y₀).toAffine.addX (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
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
  have hNpp := velu2_tangent_addX_cleared_identity hP hQ hord

  rw [velu2_tan_quotSlope_eq hgy hx hy hY]
  conv_lhs => rw [velu2X, add_comm]
  rw [← eq_sub_iff_add_eq, div_eq_iff (sub_ne_zero.mpr hx2), ← sub_eq_zero]
  simp only [velu2X, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, WeierstrassCurve.Affine.addX, veluQuotient2_a₁,
    veluQuotient2_a₂]
  field_simp
  simp only [WeierstrassCurve.Affine.negY]
  linear_combination -veluGx W x₀ y₀ * hNpp

end Field


end
end Dubon2026.SourceEllipticVelu

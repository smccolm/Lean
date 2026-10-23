import Dubon2026.SourceEllipticVeluTwoCollisionCases

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

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
  {x₀ y₀ x₁ y₁ x₂ y₂ : F}

theorem velu2_secX_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : velu2X W x₀ y₀ x₁ ≠ velu2X W x₀ y₀ x₂) :
    velu2X W x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (veluQuotient2 W x₀ y₀).toAffine.addX (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
          ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
            (velu2Y W x₀ y₀ x₁ y₁) (velu2Y W x₀ y₀ x₂ y₂)) := by
  have hSI2 := velu2_secX_SI2 hP₁ hP₂ hQ hord
  have hSI3 := velu2_secX_SI3 hP₁ hP₂ hQ hord
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : velu2X W x₀ y₀ x₁ - velu2X W x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12
  have hD₁₂ : (x₁ - x₀) * (x₂ - x₀) - veluGx W x₀ y₀ ≠ 0 := fun h =>
    hX12' (by rw [velu2X_sub_velu2X hx₁ hx₂, h, mul_zero, zero_div])
  have hdA : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀ ≠ 0 := sub_ne_zero.mpr hsp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hX12, velu2X_sub_velu2X hx₁ hx₂]

  conv_lhs => rw [velu2X, add_comm]
  rw [← eq_sub_iff_add_eq, div_eq_iff hdA, ← sub_eq_zero]

  simp only [velu2X, velu2Y, WeierstrassCurve.Affine.slope_of_X_ne hx12, WeierstrassCurve.Affine.addX, veluQuotient2_a₁,
    veluQuotient2_a₂]
  field_simp [hd₁, hd₂, hd₁₂, hD₁₂]
  linear_combination
    (veluGx W x₀ y₀ * (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - veluGx W x₀ y₀) * ((x₁ - x₂) ^ 2 * ((x₁ - x₀) * (x₂ - x₀)) + ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2) * ((x₁ - x₀) + (x₂ - x₀)))) * hSI2
    + (-(veluGx W x₀ y₀ * (x₁ - x₂) ^ 2 * ((x₁ - x₀) * (x₂ - x₀)) * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀) + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀) - W.a₁ * ((x₁ - x₀) * (x₂ - x₀))))) * hSI3

theorem velu2_secY_negAddY_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : velu2X W x₀ y₀ x₁ ≠ velu2X W x₀ y₀ x₂) :
    velu2Y W x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (veluQuotient2 W x₀ y₀).toAffine.negAddY (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
          (velu2Y W x₀ y₀ x₁ y₁)
          ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
            (velu2Y W x₀ y₀ x₁ y₁) (velu2Y W x₀ y₀ x₂ y₂)) := by
  have hSIY := velu2_secant_negAddY_cleared_identity hP₁ hP₂ hQ hord hx12
  have hXalign := velu2_secX_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : velu2X W x₀ y₀ x₁ - velu2X W x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12
  have hdA : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀ ≠ 0 := sub_ne_zero.mpr hsp

  have hColQ :
      (velu2X W x₀ y₀ x₂ - velu2X W x₀ y₀ x₁)
          * (velu2Y W x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
                (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
              - velu2Y W x₀ y₀ x₁ y₁)
        = (velu2X W x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
              - velu2X W x₀ y₀ x₁)
          * (velu2Y W x₀ y₀ x₂ y₂ - velu2Y W x₀ y₀ x₁ y₁) := by

    set xA := W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) with hxA_def
    set nAY := W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) with hnAY_def

    have hxA_rel : (x₁ - x₂) ^ 2 * (xA - x₀)
        = (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂)
            - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
      rw [hxA_def]; simp only [WeierstrassCurve.Affine.slope_of_X_ne hx12, WeierstrassCurve.Affine.addX]; field_simp; ring
    have hnAY_rel : (x₁ - x₂) * (nAY - y₁) = (y₁ - y₂) * (xA - x₁) := by
      rw [hnAY_def, hxA_def]
      simp only [WeierstrassCurve.Affine.slope_of_X_ne hx12, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negAddY]; field_simp; ring
    simp only [velu2X, velu2Y]
    field_simp [hd₁, hd₂, hdA]
    refine mul_left_cancel₀ (pow_ne_zero 2 hd₁₂) ?_
    linear_combination
      ((veluGx W x₀ y₀) * (x₁ - x₀) * (x₁ - x₂) * ((x₁ - x₂)^2 * (W.a₂ + 2*x₁ + x₂) - (y₁ - y₂)^2 - W.a₁ * (y₁ - y₂) * (x₁ - x₂))) * hSIY
      + ((veluGx W x₀ y₀) * (x₁ - x₀) * (x₂ - xA) * (W.a₁*x₀^3*x₁ - W.a₁*x₀^3*x₂ - W.a₁*x₀^2*x₁^2 - W.a₁*x₀^2*x₁*xA + W.a₁*x₀^2*x₂^2 + W.a₁*x₀^2*x₂*xA + W.a₁*x₀*x₁^2*x₂ + W.a₁*x₀*x₁^2*xA - W.a₁*x₀*x₁*x₂^2 - W.a₁*x₀*x₂^2*xA - W.a₁*x₁^2*x₂*xA + W.a₁*x₁*x₂^2*xA + (veluGx W x₀ y₀)*x₀*y₁ - (veluGx W x₀ y₀)*x₀*y₂ - (veluGx W x₀ y₀)*x₁*y₀ + (veluGx W x₀ y₀)*x₁*y₂ + (veluGx W x₀ y₀)*x₂*y₀ - (veluGx W x₀ y₀)*x₂*y₁ - x₀^3*y₁ + x₀^3*y₂ + 3*x₀^2*x₁*y₀ - 3*x₀^2*x₁*y₂ - 3*x₀^2*x₂*y₀ + 3*x₀^2*x₂*y₁ - 2*x₀*x₁^2*y₀ + 2*x₀*x₁^2*y₂ - x₀*x₁*x₂*y₁ + x₀*x₁*x₂*y₂ - 2*x₀*x₁*xA*y₀ + x₀*x₁*xA*y₁ + x₀*x₁*xA*y₂ + 2*x₀*x₂^2*y₀ - 2*x₀*x₂^2*y₁ + 2*x₀*x₂*xA*y₀ - x₀*x₂*xA*y₁ - x₀*x₂*xA*y₂ + x₁^2*x₂*y₀ - x₁^2*x₂*y₂ + x₁^2*xA*y₀ - x₁^2*xA*y₂ - x₁*x₂^2*y₀ + x₁*x₂^2*y₁ - x₁*x₂*xA*y₁ + x₁*x₂*xA*y₂ - x₂^2*xA*y₀ + x₂^2*xA*y₁)) * hxA_rel
      + ((x₁ - x₀) * (x₂ - x₀) * ((x₁ - x₀)*(x₂ - x₀) - (veluGx W x₀ y₀)) * (W.a₁*(veluGx W x₀ y₀)*x₁*y₁ - W.a₁*(veluGx W x₀ y₀)*x₁*y₂ - W.a₁*(veluGx W x₀ y₀)*x₂*y₁ + W.a₁*(veluGx W x₀ y₀)*x₂*y₂ - W.a₂*(veluGx W x₀ y₀)*x₁^2 + 2*W.a₂*(veluGx W x₀ y₀)*x₁*x₂ - W.a₂*(veluGx W x₀ y₀)*x₂^2 - (veluGx W x₀ y₀)*x₀*x₁^2 + 2*(veluGx W x₀ y₀)*x₀*x₁*x₂ - (veluGx W x₀ y₀)*x₀*x₂^2 - (veluGx W x₀ y₀)*x₁^3 + (veluGx W x₀ y₀)*x₁^2*x₂ + (veluGx W x₀ y₀)*x₁*x₂^2 - (veluGx W x₀ y₀)*x₂^3 + (veluGx W x₀ y₀)*y₁^2 - 2*(veluGx W x₀ y₀)*y₁*y₂ + (veluGx W x₀ y₀)*y₂^2 + x₀^3*x₁^2 - 2*x₀^3*x₁*x₂ + x₀^3*x₂^2 - x₀^2*x₁^3 + 2*x₀^2*x₁^2*x₂ - 2*x₀^2*x₁^2*xA - x₀^2*x₁*x₂^2 + 4*x₀^2*x₁*x₂*xA - 2*x₀^2*x₂^2*xA + 2*x₀*x₁^3*xA - 4*x₀*x₁^2*x₂*xA + x₀*x₁^2*xA^2 + 2*x₀*x₁*x₂^2*xA - 2*x₀*x₁*x₂*xA^2 + x₀*x₂^2*xA^2 - x₁^3*xA^2 + 2*x₁^2*x₂*xA^2 - x₁*x₂^2*xA^2)) * hnAY_rel

  conv_rhs => rw [WeierstrassCurve.Affine.negAddY, ← hXalign, WeierstrassCurve.Affine.slope_of_X_ne hX12]
  field_simp
  linear_combination -hColQ

theorem velu2_secY_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : velu2X W x₀ y₀ x₁ ≠ velu2X W x₀ y₀ x₂) :
    velu2Y W x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (veluQuotient2 W x₀ y₀).toAffine.addY (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
          (velu2Y W x₀ y₀ x₁ y₁)
          ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
            (velu2Y W x₀ y₀ x₁ y₁) (velu2Y W x₀ y₀ x₂ y₂)) := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hXalign := velu2_secX_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  have hnAY := velu2_secY_negAddY_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  rw [WeierstrassCurve.Affine.addY, velu2Y_negY hgy, WeierstrassCurve.Affine.addY, hXalign, hnAY]

end Field


end
end Dubon2026.SourceEllipticVelu

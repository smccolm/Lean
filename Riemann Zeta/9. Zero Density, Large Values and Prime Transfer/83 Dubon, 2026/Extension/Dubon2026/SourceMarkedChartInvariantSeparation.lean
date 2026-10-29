import Dubon2026.SourceMarkedChartVariableInvariants

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original-field
marked-point stabilizer. The two actual coordinate invariants determine
the abscissa in every characteristic. When 12 vanishes, the second invariant
and nonvanishing c4 supply the missing linear coefficient. Native X_eq_iff
then identifies the actual elliptic points up to sign. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve
variable {K : Type*} [Field K] (W : WeierstrassCurve K)

theorem abscissa_eq_of_invariant_pair (hc4 : W.c₄ ≠ 0) (hc6 : W.c₆ ≠ 0)
    {x z : K}
    (h1 : W.c₄ * (12 * x + W.b₂) / W.c₆ = W.c₄ * (12 * z + W.b₂) / W.c₆)
    (h2 : (6 * x ^ 2 + W.b₂ * x + W.b₄) / W.c₄ =
      (6 * z ^ 2 + W.b₂ * z + W.b₄) / W.c₄) : x = z := by
  have hl : 12 * x + W.b₂ = 12 * z + W.b₂ :=
    mul_left_cancel₀ hc4 ((div_left_inj' hc6).mp h1)
  by_cases h12 : (12 : K) = 0
  · have h6sq : (6 : K) ^ 2 = 0 := by
      calc
        (6 : K) ^ 2 = 3 * 12 := by ring
        _ = 0 := by rw [h12, mul_zero]
    have h6 : (6 : K) = 0 := sq_eq_zero_iff.mp h6sq
    have h24 : (24 : K) = 0 := by
      calc
        (24 : K) = 2 * 12 := by ring
        _ = 0 := by rw [h12, mul_zero]
    have hb2 : W.b₂ ≠ 0 := by
      intro hb
      apply hc4
      rw [WeierstrassCurve.c₄, hb, h24]
      ring
    have he := (div_left_inj' hc4).mp h2
    simp only [h6, zero_mul, zero_add] at he
    exact mul_left_cancel₀ hb2 (add_right_cancel he)
  · exact mul_left_cancel₀ h12 (add_right_cancel hl)

theorem point_eq_or_neg_of_invariant_pair (hc4 : W.c₄ ≠ 0) (hc6 : W.c₆ ≠ 0)
    {x y z w : K} (hxy : W.toAffine.Nonsingular x y) (hzw : W.toAffine.Nonsingular z w)
    (h1 : W.c₄ * (12 * x + W.b₂) / W.c₆ = W.c₄ * (12 * z + W.b₂) / W.c₆)
    (h2 : (6 * x ^ 2 + W.b₂ * x + W.b₄) / W.c₄ =
      (6 * z ^ 2 + W.b₂ * z + W.b₄) / W.c₄) :
    Affine.Point.some x y hxy = Affine.Point.some z w hzw ∨
      Affine.Point.some x y hxy = -Affine.Point.some z w hzw :=
  Affine.Point.X_eq_iff.mp (abscissa_eq_of_invariant_pair W hc4 hc6 h1 h2)

end
end Dubon2026.SourceFunctionField.MarkedChart

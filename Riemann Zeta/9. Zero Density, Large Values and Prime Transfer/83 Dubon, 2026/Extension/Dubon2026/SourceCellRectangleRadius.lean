import Dubon2026.SourceCellRectangleAngles

/-! DUB-17/18 -> original Abel-Jacobi -> paired analytic cell dissection.
The literal rectangle radius, its side formulas and piecewise smoothness
supply the required six-arc rectangle. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RectRadial
open Real
variable {a b c d : ℝ}

private theorem le_inv_iff_aux {a D : ℝ} (hD : 0 < D) :
    a ≤ D⁻¹ ↔ a * D ≤ 1 := by
  constructor
  · intro h
    calc a * D ≤ D⁻¹ * D := by gcongr
    _ = 1 := inv_mul_cancel₀ hD.ne'
  · intro h
    have h2 : a * D * D⁻¹ ≤ 1 * D⁻¹ := by gcongr
    calc a = a * D * D⁻¹ := by field_simp
    _ ≤ 1 * D⁻¹ := h2
    _ = D⁻¹ := one_mul _

private theorem lt_inv_iff_aux {a D : ℝ} (hD : 0 < D) :
    a < D⁻¹ ↔ a * D < 1 := by
  rw [← not_le, ← not_le]
  refine not_congr ?_
  constructor
  · intro h
    calc 1 = D⁻¹ * D := (inv_mul_cancel₀ hD.ne').symm
    _ ≤ a * D := by gcongr
  · intro h
    calc D⁻¹ = D⁻¹ * 1 := (mul_one _).symm
    _ ≤ D⁻¹ * (a * D) := by gcongr
    _ = a * (D⁻¹ * D) := by ring
    _ = a := by rw [inv_mul_cancel₀ hD.ne', mul_one]


/- As constructed below. -/
/-- The exact radial distance to an axis-aligned rectangle boundary. -/
noncomputable def rectRadial4 (a b c d : ℝ) (ψ : ℝ) : ℝ :=
  (max (max (Real.cos ψ / a) (-Real.cos ψ / b)) (max (Real.sin ψ / c) (-Real.sin ψ / d)))⁻¹

theorem rectRadial4_denom_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (ψ : ℝ) :
    0 < max (max (Real.cos ψ / a) (-Real.cos ψ / b))
        (max (Real.sin ψ / c) (-Real.sin ψ / d)) := by
  rcases lt_trichotomy (Real.cos ψ) 0 with h | h | h
  · exact lt_max_of_lt_left (lt_max_of_lt_right (div_pos (by linarith) hb))
  · have hs : Real.sin ψ ≠ 0 := by
      intro hs0
      have := Real.sin_sq_add_cos_sq ψ
      rw [h, hs0] at this
      norm_num at this
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · exact lt_max_of_lt_right (lt_max_of_lt_right (div_pos (by linarith) hd))
    · exact lt_max_of_lt_right (lt_max_of_lt_left (div_pos hpos hc))
  · exact lt_max_of_lt_left (lt_max_of_lt_left (div_pos h ha))

theorem rectRadial4_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (ψ : ℝ) :
    0 < rectRadial4 a b c d ψ :=
  inv_pos.mpr (rectRadial4_denom_pos ha hb hc hd ψ)

theorem continuous_rectRadial4 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Continuous (rectRadial4 a b c d) := by
  refine Continuous.inv₀ ?_ (fun ψ => (rectRadial4_denom_pos ha hb hc hd ψ).ne')
  exact ((Real.continuous_cos.div_const a).max
      ((Real.continuous_cos.neg.div_const b))).max
    ((Real.continuous_sin.div_const c).max ((Real.continuous_sin.neg.div_const d)))

theorem periodic_rectRadial4 :
    Function.Periodic (rectRadial4 a b c d) (2 * π) := by
  intro ψ
  unfold rectRadial4
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem mem_rectRadial4_iff (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p z : ℂ) :
    ‖z - p‖ ≤ rectRadial4 a b c d (Complex.arg (z - p)) ↔
      z.re - p.re ∈ Set.Icc (-b) a ∧ z.im - p.im ∈ Set.Icc (-d) c := by
  set w := z - p with hw
  have hD := rectRadial4_denom_pos ha hb hc hd (Complex.arg w)
  rw [rectRadial4, le_inv_iff_aux hD]
  have hre : ‖w‖ * Real.cos (Complex.arg w) = w.re := Complex.norm_mul_cos_arg w
  have him : ‖w‖ * Real.sin (Complex.arg w) = w.im := Complex.norm_mul_sin_arg w
  have hnn : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
  have hwre : z.re - p.re = w.re := by rw [hw]; simp
  have hwim : z.im - p.im = w.im := by rw [hw]; simp
  rw [mul_max_of_nonneg _ _ hnn, mul_max_of_nonneg _ _ hnn, mul_max_of_nonneg _ _ hnn]
  have e1 : ‖w‖ * (Real.cos (Complex.arg w) / a) = w.re / a := by
    rw [← mul_div_assoc, hre]
  have e2 : ‖w‖ * (-Real.cos (Complex.arg w) / b) = -w.re / b := by
    rw [← mul_div_assoc, mul_neg, hre]
  have e3 : ‖w‖ * (Real.sin (Complex.arg w) / c) = w.im / c := by
    rw [← mul_div_assoc, him]
  have e4 : ‖w‖ * (-Real.sin (Complex.arg w) / d) = -w.im / d := by
    rw [← mul_div_assoc, mul_neg, him]
  rw [e1, e2, e3, e4, hwre, hwim, max_le_iff, max_le_iff, max_le_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [(div_le_one hb).mp h2]
    · exact (div_le_one ha).mp h1
    · linarith [(div_le_one hd).mp h4]
    · exact (div_le_one hc).mp h3
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (div_le_one ha).mpr h2
    · rw [div_le_one hb]; linarith
    · exact (div_le_one hc).mpr h4
    · rw [div_le_one hd]; linarith

theorem mem_rectRadial4_lt_iff (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p z : ℂ) :
    ‖z - p‖ < rectRadial4 a b c d (Complex.arg (z - p)) ↔
      z.re - p.re ∈ Set.Ioo (-b) a ∧ z.im - p.im ∈ Set.Ioo (-d) c := by
  set w := z - p with hw
  have hD := rectRadial4_denom_pos ha hb hc hd (Complex.arg w)
  rw [rectRadial4, lt_inv_iff_aux hD]
  have hre : ‖w‖ * Real.cos (Complex.arg w) = w.re := Complex.norm_mul_cos_arg w
  have him : ‖w‖ * Real.sin (Complex.arg w) = w.im := Complex.norm_mul_sin_arg w
  have hnn : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
  have hwre : z.re - p.re = w.re := by rw [hw]; simp
  have hwim : z.im - p.im = w.im := by rw [hw]; simp
  rw [mul_max_of_nonneg _ _ hnn, mul_max_of_nonneg _ _ hnn, mul_max_of_nonneg _ _ hnn]
  have e1 : ‖w‖ * (Real.cos (Complex.arg w) / a) = w.re / a := by
    rw [← mul_div_assoc, hre]
  have e2 : ‖w‖ * (-Real.cos (Complex.arg w) / b) = -w.re / b := by
    rw [← mul_div_assoc, mul_neg, hre]
  have e3 : ‖w‖ * (Real.sin (Complex.arg w) / c) = w.im / c := by
    rw [← mul_div_assoc, him]
  have e4 : ‖w‖ * (-Real.sin (Complex.arg w) / d) = -w.im / d := by
    rw [← mul_div_assoc, mul_neg, him]
  rw [e1, e2, e3, e4, hwre, hwim, max_lt_iff, max_lt_iff, max_lt_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [(div_lt_one hb).mp h2]
    · exact (div_lt_one ha).mp h1
    · linarith [(div_lt_one hd).mp h4]
    · exact (div_lt_one hc).mp h3
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (div_lt_one ha).mpr h2
    · rw [div_lt_one hb]; linarith
    · exact (div_lt_one hc).mpr h4
    · rw [div_lt_one hd]; linarith


end Dubon2026.SourceFunctionField.CellGeometry.RectRadial

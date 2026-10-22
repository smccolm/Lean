import Dubon2026.SourceCellRectangleRadius

/-! DUB-17/18 -> original Abel-Jacobi -> paired analytic cell dissection.
The literal rectangle radius, its side formulas and piecewise smoothness
supply the required six-arc rectangle. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RectRadial
open Real
variable {a b c d : ℝ}

private theorem div_le_div_of_mul_le {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  refine le_of_mul_le_mul_right ?_ (mul_pos hb hd)
  have e1 : a / b * (b * d) = a * d := by
    rw [← mul_assoc, div_mul_cancel₀ a hb.ne']
  have e2 : c / d * (b * d) = c * b := by
    rw [mul_comm b d, ← mul_assoc, div_mul_cancel₀ c hd.ne']
  rw [e1, e2]
  exact h


private theorem branch_le_of_mul_le {X Y P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (h : X * Q ≤ Y * P) : X / P ≤ Y / Q :=
  div_le_div_of_mul_le hP hQ h

theorem collapse_arc1 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ cornerAngle a c) :
    rectRadial4 a b c d ψ = (Real.cos ψ / a)⁻¹ := by
  have hψ2 : cornerAngle a c < π / 2 := cornerAngle_lt_pi_div_two a c
  have hcos : 0 ≤ Real.cos ψ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsin : 0 ≤ Real.sin ψ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hcore := core_cos ha hc (show |ψ| ≤ cornerAngle a c by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg hsin] at hcore
  unfold rectRadial4
  congr 1
  rw [max_eq_left (le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcos) hb.le)
    (div_nonneg hcos ha.le))]
  refine max_eq_left (max_le ?_ ?_)
  · exact branch_le_of_mul_le hc ha (by nlinarith)
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsin) hd.le) (div_nonneg hcos ha.le)

theorem collapse_arc2 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {ψ : ℝ} (h0 : cornerAngle a c ≤ ψ) (h1 : ψ ≤ π - cornerAngle b c) :
    rectRadial4 a b c d ψ = (Real.sin ψ / c)⁻¹ := by
  have hac2 : cornerAngle a c < π / 2 := cornerAngle_lt_pi_div_two a c
  have hbc2 : cornerAngle b c < π / 2 := cornerAngle_lt_pi_div_two b c
  have hac0 : 0 < cornerAngle a c := cornerAngle_pos ha hc
  have hbc0 : 0 < cornerAngle b c := cornerAngle_pos hb hc
  have hsin : 0 ≤ Real.sin ψ :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hca : Real.cos ψ / a ≤ Real.sin ψ / c := by
    rcases le_total ψ (π / 2) with hhalf | hhalf
    · have hcore := core_sin ha hc h0 (by linarith)
      have habs : Real.cos ψ ≤ |Real.cos ψ| := le_abs_self _
      exact branch_le_of_mul_le ha hc (by nlinarith)
    · have hcos : Real.cos ψ ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith [Real.pi_pos])
      exact le_trans (div_nonpos_of_nonpos_of_nonneg hcos ha.le) (div_nonneg hsin hc.le)
  have hcb : -Real.cos ψ / b ≤ Real.sin ψ / c := by
    rcases le_total ψ (π / 2) with hhalf | hhalf
    · have hcos : 0 ≤ Real.cos ψ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, hhalf⟩
      exact le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcos) hb.le) (div_nonneg hsin hc.le)
    · have hcore := core_sin hb hc (by linarith) h1
      have hcos : Real.cos ψ ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith [Real.pi_pos])
      rw [abs_of_nonpos hcos] at hcore
      exact branch_le_of_mul_le hb hc (by nlinarith)
  unfold rectRadial4
  congr 1
  rw [max_eq_left (le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsin) hd.le)
    (div_nonneg hsin hc.le))]
  exact max_eq_right (max_le hca hcb)

theorem collapse_arc3 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {ψ : ℝ} (h0 : π - cornerAngle b c ≤ ψ) (h1 : ψ ≤ π + cornerAngle b d) :
    rectRadial4 a b c d ψ = (-Real.cos ψ / b)⁻¹ := by
  have hbc2 : cornerAngle b c < π / 2 := cornerAngle_lt_pi_div_two b c
  have hbd2 : cornerAngle b d < π / 2 := cornerAngle_lt_pi_div_two b d
  set s : ℝ := ψ - π with hs_def
  have hcos : Real.cos ψ = -Real.cos s := by
    rw [show ψ = s + π by rw [hs_def]; ring, Real.cos_add_pi]
  have hsin : Real.sin ψ = -Real.sin s := by
    rw [show ψ = s + π by rw [hs_def]; ring, Real.sin_add_pi]
  have hsr1 : -cornerAngle b c ≤ s := by rw [hs_def]; linarith
  have hsr2 : s ≤ cornerAngle b d := by rw [hs_def]; linarith
  have hcoss : 0 ≤ Real.cos s :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  unfold rectRadial4
  congr 1
  rw [hcos, hsin, neg_neg, neg_neg]
  have hA : -Real.cos s / a ≤ Real.cos s / b :=
    le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoss) ha.le) (div_nonneg hcoss hb.le)
  have hC : -Real.sin s / c ≤ Real.cos s / b := by
    rcases le_total 0 s with hpos | hneg
    · have hsp : 0 ≤ Real.sin s :=
        Real.sin_nonneg_of_nonneg_of_le_pi hpos (by linarith [Real.pi_pos])
      exact le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsp) hc.le) (div_nonneg hcoss hb.le)
    · have hcore := core_cos hb hc
        (show |s| ≤ cornerAngle b c by rw [abs_of_nonpos hneg]; linarith)
      rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg
        (by linarith [Real.pi_pos]))] at hcore
      exact branch_le_of_mul_le hc hb (by nlinarith)
  have hD : Real.sin s / d ≤ Real.cos s / b := by
    rcases le_total 0 s with hpos | hneg
    · have hcore := core_cos hb hd
        (show |s| ≤ cornerAngle b d by rw [abs_of_nonneg hpos]; exact hsr2)
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hpos
        (by linarith [Real.pi_pos]))] at hcore
      exact branch_le_of_mul_le hd hb (by nlinarith)
    · have hsp : Real.sin s ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg (by linarith [Real.pi_pos])
      exact le_trans (div_nonpos_of_nonpos_of_nonneg hsp hd.le) (div_nonneg hcoss hb.le)
  rw [max_eq_right hA]
  exact max_eq_left (max_le hC hD)

theorem collapse_arc4 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {ψ : ℝ} (h0 : π + cornerAngle b d ≤ ψ) (h1 : ψ ≤ 2 * π - cornerAngle a d) :
    rectRadial4 a b c d ψ = (-Real.sin ψ / d)⁻¹ := by
  have hbd2 : cornerAngle b d < π / 2 := cornerAngle_lt_pi_div_two b d
  have had2 : cornerAngle a d < π / 2 := cornerAngle_lt_pi_div_two a d
  have hbd0 : 0 < cornerAngle b d := cornerAngle_pos hb hd
  have had0 : 0 < cornerAngle a d := cornerAngle_pos ha hd
  set s : ℝ := ψ - π with hs_def
  have hcos : Real.cos ψ = -Real.cos s := by
    rw [show ψ = s + π by rw [hs_def]; ring, Real.cos_add_pi]
  have hsin : Real.sin ψ = -Real.sin s := by
    rw [show ψ = s + π by rw [hs_def]; ring, Real.sin_add_pi]
  have hsr1 : cornerAngle b d ≤ s := by rw [hs_def]; linarith
  have hsr2 : s ≤ π - cornerAngle a d := by rw [hs_def]; linarith
  have hsins : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  unfold rectRadial4
  congr 1
  rw [hcos, hsin, neg_neg, neg_neg]
  have hA : -Real.cos s / a ≤ Real.sin s / d := by
    rcases le_total s (π / 2) with hhalf | hhalf
    · have hcp : 0 ≤ Real.cos s :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hhalf⟩
      exact le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcp) ha.le) (div_nonneg hsins hd.le)
    · have hcore := core_sin ha hd (by linarith) hsr2
      rw [abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le hhalf
        (by linarith [Real.pi_pos]))] at hcore
      exact branch_le_of_mul_le ha hd (by nlinarith)
  have hB : Real.cos s / b ≤ Real.sin s / d := by
    rcases le_total s (π / 2) with hhalf | hhalf
    · have hcore := core_sin hb hd hsr1 (by linarith)
      rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos], hhalf⟩)] at hcore
      exact branch_le_of_mul_le hb hd (by nlinarith)
    · have hcp : Real.cos s ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith [Real.pi_pos])
      exact le_trans (div_nonpos_of_nonpos_of_nonneg hcp hb.le) (div_nonneg hsins hd.le)
  have hC : -Real.sin s / c ≤ Real.sin s / d :=
    le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsins) hc.le) (div_nonneg hsins hd.le)
  rw [max_eq_right hC]
  exact max_eq_right (max_le hA hB)

theorem collapse_arc5 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {ψ : ℝ} (h0 : 2 * π - cornerAngle a d ≤ ψ) (h1 : ψ ≤ 2 * π) :
    rectRadial4 a b c d ψ = (Real.cos ψ / a)⁻¹ := by
  have had2 : cornerAngle a d < π / 2 := cornerAngle_lt_pi_div_two a d
  set s : ℝ := ψ - 2 * π with hs_def
  have hcos : Real.cos ψ = Real.cos s := by
    rw [show ψ = s + 2 * π by rw [hs_def]; ring, Real.cos_add_two_pi]
  have hsin : Real.sin ψ = Real.sin s := by
    rw [show ψ = s + 2 * π by rw [hs_def]; ring, Real.sin_add_two_pi]
  have hsr1 : -cornerAngle a d ≤ s := by rw [hs_def]; linarith
  have hsr2 : s ≤ 0 := by rw [hs_def]; linarith
  have hcoss : 0 ≤ Real.cos s :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hsins : Real.sin s ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hsr2 (by linarith [Real.pi_pos])
  have hcore := core_cos ha hd (show |s| ≤ cornerAngle a d by rw [abs_of_nonpos hsr2]; linarith)
  rw [abs_of_nonpos hsins] at hcore
  unfold rectRadial4
  congr 1
  rw [hcos, hsin]
  rw [max_eq_left (le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoss) hb.le)
    (div_nonneg hcoss ha.le))]
  refine max_eq_left (max_le ?_ ?_)
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hsins hc.le) (div_nonneg hcoss ha.le)
  · exact branch_le_of_mul_le hd ha (by nlinarith)

end Dubon2026.SourceFunctionField.CellGeometry.RectRadial

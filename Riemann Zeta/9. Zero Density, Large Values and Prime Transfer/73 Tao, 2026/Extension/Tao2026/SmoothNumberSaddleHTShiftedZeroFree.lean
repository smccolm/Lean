import Tao2026.SmoothNumberSaddleHTShiftedRectangle
import GafniTao.FordAsymptoticZeroFree

/-!
# Vinogradov--Korobov zero-free input for the shifted HT rectangle

This module transports the frozen rectangle-uniform zero-free region to the
translated variable `w = (1-beta+i*t) + z`.  With left edge `beta-eta`, the
physical zeta rectangle begins at `Re w = 1-eta`; its height is bounded by
`|t|+T`.  The frozen Vinogradov--Korobov width therefore discharges the
literal surrogate-zero-free premise of the exact shifted rectangle theorem.

The final theorem also extracts native constants from the proved Ford
zero-free theorem.  Choosing HT parameters that satisfy the displayed width
condition and bounding the three contour edges remain separate steps.
-/

open Complex Set

namespace Tao2026

noncomputable section

theorem smoothSaddleHTSource_shiftedSurrogate_ne_zero_on_rectangle_of_vK
    {c H eta beta t T right : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hetaOne : eta ≤ 1)
    (hleftRight : beta - eta ≤ right) (hT : 0 ≤ T)
    (hHeight : H ≤ |t| + T)
    (hWidth : eta ≤ c /
      GafniTao.vinogradovKorobovDenominator (|t| + T)) :
    ∀ z ∈ Rectangle
        (((beta - eta : ℝ) : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t + z) ≠ 0 := by
  intro z hz hsur
  let w : ℂ := smoothSaddleHTSourceExponent beta t + z
  have hzReRaw := hz.1
  have hzImRaw := hz.2
  have hzRe : z.re ∈ Set.Icc (beta - eta) right := by
    have : z.re ∈ Set.uIcc (beta - eta) right := by simpa using hzReRaw
    simpa [Set.uIcc_of_le hleftRight] using this
  have hTorder : -T ≤ T := by linarith
  have hzIm : z.im ∈ Set.Icc (-T) T := by
    have : z.im ∈ Set.uIcc (-T) T := by simpa using hzImRaw
    simpa [Set.uIcc_of_le hTorder] using this
  have hwReLower : 1 - eta ≤ w.re := by
    dsimp [w]
    simp [smoothSaddleHTSourceExponent]
    linarith [hzRe.1]
  have hwIm : w.im = t + z.im := by
    dsimp [w]
    simp [smoothSaddleHTSourceExponent]
  have hwAbsIm : |w.im| ≤ |t| + T := by
    rw [hwIm]
    calc
      |t + z.im| ≤ |t| + |z.im| := abs_add_le _ _
      _ ≤ |t| + T := by gcongr; exact abs_le.mpr hzIm
  have hsurW : GafniTao.sharpZetaSurrogate w = 0 := by
    simpa [w] using hsur
  by_cases hw1 : w = 1
  · rw [hw1, GafniTao.sharpZetaSurrogate_one] at hsurW
    exact one_ne_zero hsurW
  · have hzeta : riemannZeta w = 0 :=
      (GafniTao.sharpZetaSurrogate_eq_zero_iff hw1).mp hsurW
    by_cases hwOne : 1 ≤ w.re
    · exact (riemannZeta_ne_zero_of_one_le_re hwOne) hzeta
    · have hwReUpper : w.re ≤ 1 := (lt_of_not_ge hwOne).le
      have hwReZero : 0 ≤ w.re := by linarith
      have hwZeroSet : w ∈ GafniTao.zeroSet 0 (|t| + T) := by
        change w ∈ RiemannZeta.GuthMaynard.zerosInRect
          0 1 (-(|t| + T)) (|t| + T)
        rw [RiemannZeta.GuthMaynard.zerosInRect,
          Set.Finite.mem_toFinset, Set.mem_inter_iff]
        refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
          0 1 (-(|t| + T)) (|t| + T) w).mpr ?_, hzeta⟩
        exact ⟨hwReZero, hwReUpper, (abs_le.mp hwAbsIm).1,
          (abs_le.mp hwAbsIm).2⟩
      have hZeroRight := (hZeroFree hHeight).2.2 hwZeroSet
      linarith

theorem smoothSaddleHTSource_shiftedPerron_rightLine_eq_main_add_edges_of_vK
    {c H eta beta t T right : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hy : 0 < y) (heta : 0 < eta) (hetaBeta : eta < beta)
    (hetaOne : eta ≤ 1) (hbetaRight : beta < right)
    (ht : |t| < T) (hHeight : H ≤ |t| + T)
    (hWidth : eta ≤ c /
      GafniTao.vinogradovKorobovDenominator (|t| + T)) :
    (1 / (2 * Real.pi) : ℂ) *
          (∫ u in (-T)..T,
            (-deriv riemannZeta
                  (smoothSaddleHTSourceExponent beta t +
                    ((right : ℂ) + (u : ℂ) * Complex.I)) /
                riemannZeta
                  (smoothSaddleHTSourceExponent beta t +
                    ((right : ℂ) + (u : ℂ) * Complex.I))) *
              (y : ℂ) ^ ((right : ℂ) + (u : ℂ) * Complex.I) /
                ((right : ℂ) + (u : ℂ) * Complex.I)) =
      smoothSaddleHTSourceMainTerm y
          (smoothSaddleHTSourceExponent beta t) -
        HIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t))
            (beta - eta) right (-T) +
        HIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t))
            (beta - eta) right T +
        VIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t))
            (beta - eta) (-T) T := by
  apply smoothSaddleHTSource_shiftedPerron_rightLine_eq_main_add_edges
    hy (by linarith) (by linarith) hbetaRight ht
  apply smoothSaddleHTSource_shiftedSurrogate_ne_zero_on_rectangle_of_vK
    hZeroFree hetaOne (by linarith) (le_of_lt (abs_nonneg t |>.trans_lt ht))
    hHeight hWidth

theorem exists_smoothSaddleHT_native_vinogradovKorobovRectangleZeroFree :
    ∃ c H : ℝ, 0 < c ∧ Real.exp (Real.exp 1) ≤ H ∧
      GafniTao.VinogradovKorobovRectangleZeroFree c H := by
  obtain ⟨c₀, H, hc₀, hH, hPointwise⟩ :=
    GafniTao.ford_asymptotic_zero_free_native
  obtain ⟨c, hc, _hcLe, hRectangle⟩ :=
    GafniTao.exists_vinogradovKorobovRectangleZeroFree_of_pointwise
      hc₀ hH hPointwise
  exact ⟨c, H, hc, hH, hRectangle⟩

end

end Tao2026

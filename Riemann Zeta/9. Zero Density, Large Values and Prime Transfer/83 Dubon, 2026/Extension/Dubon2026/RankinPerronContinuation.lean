import Dubon2026.RankinStripPhragmenLindelof
import Dubon2026.RankinConvolutionPerron

/-! # The actual continued Rankin Perron integrand and its sharp strip decay -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- Nonzero height excludes every real translate from zero. -/
theorem rankinContour_translate_ne_zero {s : ℂ} (hs : s.im ≠ 0) (a : ℝ) : s + (a : ℂ) ≠ 0 := by
  intro h
  apply hs
  simpa using congrArg Complex.im h

/-- The four actual Rankin Perron denominator factors dominate the fourth power of the height. -/
theorem rankinPerron_denominator_norm_lower (s : ℂ) :
    |s.im| ^ 4 ≤ ‖(s - 1) * (s * (s + 1) * (s + 2))‖ := by
  have h0 := Complex.abs_im_le_norm s
  have hm : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s - 1)
  have h1 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  have h2 : |s.im| ≤ ‖s + 2‖ := by simpa using Complex.abs_im_le_norm (s + 2)
  simp only [norm_mul]
  calc
    _ = |s.im| * (|s.im| * |s.im| * |s.im|) := by ring
    _ ≤ _ := by gcongr

/-- The true Rankin series divided by the cubic Riesz denominator decays uniformly as the inverse square root of height. -/
theorem exists_rankinConvolution_riesz_strip_decay {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 → 1 ≤ |s.im| →
      ‖rankinConvolutionGlobalContinuation f s / (s * (s + 1) * (s + 2))‖ ≤
        C * |s.im| ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hCb⟩ := exists_rankinConvolutionEntireNumerator_polynomial_strip_bound f hk
  refine ⟨C * (5 : ℝ) ^ (7 / 2 : ℝ), by positivity, ?_⟩
  intro s hl hr ht
  have ht0 : 0 < |s.im| := by linarith
  have hnorm : ‖s + 2‖ ≤ 5 * |s.im| := by
    have h := (s + 2).norm_le_abs_re_add_abs_im
    norm_num at h
    have hab : |s.re + 2| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hn : ‖rankinConvolutionEntireNumerator f s‖ ≤
      (C * (5 : ℝ) ^ (7 / 2 : ℝ)) * |s.im| ^ (7 / 2 : ℝ) := by
    apply (hCb s hl hr).trans
    have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num : (0 : ℝ) ≤ 7 / 2)) hC.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) (abs_nonneg _)] at hh
    simpa only [mul_assoc] using hh
  have hd := rankinPerron_denominator_norm_lower s
  have hdp : 0 < ‖(s - 1) * (s * (s + 1) * (s + 2))‖ := lt_of_lt_of_le (pow_pos ht0 4) hd
  rw [rankinConvolutionGlobalContinuation, div_div, norm_div]
  apply (div_le_iff₀ hdp).mpr
  calc
    _ ≤ (C * (5 : ℝ) ^ (7 / 2 : ℝ)) * |s.im| ^ (7 / 2 : ℝ) := hn
    _ = ((C * (5 : ℝ) ^ (7 / 2 : ℝ)) * |s.im| ^ (-(1 / 2 : ℝ))) * |s.im| ^ 4 := by
      rw [← Real.rpow_ofNat |s.im| 4]
      simp only [mul_assoc]
      rw [← Real.rpow_add ht0]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

/-- The literal Rankin Perron integrand, with the proved global continuation of its actual coefficient series. -/
def rankinPerronContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (s + 2) * rankinConvolutionGlobalContinuation f s / (s * (s + 1) * (s + 2))

/-- In the original convergence half-plane this is exactly the previously proved Perron integrand. -/
theorem rankinPerronContinuation_eq_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) (x : ℝ) {s : ℂ} (hs : 1 < s.re) :
    rankinPerronContinuation f x s =
      (x : ℂ) ^ (s + 2) * LSeries (rankinConvolutionCoefficients f) s / (s * (s + 1) * (s + 2)) := by
  rw [rankinPerronContinuation, rankinConvolutionGlobalContinuation_eq_series f hk hs]

/-- The actual continued Perron integrand is holomorphic at every nonreal point for every positive cutoff. -/
theorem differentiableAt_rankinPerronContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ (rankinPerronContinuation f x) s := by
  have hs1 : s ≠ 1 := by intro he; apply hs; simp [he]
  have hs0 : s ≠ 0 := by intro he; apply hs; simp [he]
  exact (((differentiableAt_id.add_const (2 : ℂ)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).mul
    (differentiableAt_rankinConvolutionGlobalContinuation f hs1)).div (by fun_prop)
    (mul_ne_zero (mul_ne_zero hs0 (by simpa using rankinContour_translate_ne_zero hs 1))
      (by simpa using rankinContour_translate_ne_zero hs 2))

/-- The actual general-level Perron integrand has uniform inverse-square-root decay across the entire contour-shift strip. -/
theorem exists_rankinPerronContinuation_strip_decay {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 → 1 ≤ |s.im| →
      ‖rankinPerronContinuation f x s‖ ≤ C * |s.im| ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hCb⟩ := exists_rankinConvolution_riesz_strip_decay f hk
  refine ⟨Real.exp (|Real.log x| * 4) * C, mul_pos (Real.exp_pos _) hC, ?_⟩
  intro s hl hr ht
  have hp := norm_positive_cpow_le_of_abs_re hx (s := s + 2) (B := 4) (by
    norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [rankinPerronContinuation, mul_div_assoc, norm_mul]
  have hh := mul_le_mul hp (hCb s hl hr ht) (norm_nonneg _) (Real.exp_pos _).le
  simpa only [mul_assoc] using hh

end
end Dubon2026

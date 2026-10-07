import Dubon2026.RankinConvolutionGlobal
import Dubon2026.GammaInverseStripGrowth
import Dubon2026.Gamma0CuspStripBound

/-! # Actual exponential strip growth of the entire Rankin pole numerator -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- A positive real base has uniformly bounded complex powers when the real exponent is bounded. -/
theorem norm_positive_cpow_le_of_abs_re {x B : ℝ} (hx : 0 < x) {s : ℂ} (hs : |s.re| ≤ B) :
    ‖(x : ℂ) ^ s‖ ≤ Real.exp (|Real.log x| * B) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans ((abs_mul _ _).trans_le
    (mul_le_mul_of_nonneg_left hs (abs_nonneg _)))

/-- On the fixed Rankin contour strip the genuine inverse completion factor grows at most exponentially in height. -/
theorem exists_rankinConvolutionInverseFactor_strip_bound {k : ℤ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 → 1 ≤ |s.im| →
      ‖rankinConvolutionInverseFactor k s‖ ≤ C * Real.exp (2 * Real.pi * |s.im|) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  let B : ℝ := k + 2
  let G : ℝ := Real.exp ((4 + B) * (B - 1 / 4)) * (Real.Gamma (3 / 4) / Real.pi)
  let P : ℝ := Real.exp (|Real.log Real.pi| * B)
  let Q : ℝ := Real.exp (|Real.log (4 * Real.pi)| * B)
  have hG : 0 < G := mul_pos (Real.exp_pos _) (div_pos (Real.Gamma_pos_of_pos (by norm_num)) Real.pi_pos)
  refine ⟨P * Q * G ^ 2, by dsimp only [P, Q]; positivity, ?_⟩
  intro s hl hr ht
  have hp : ‖(Real.pi : ℂ) ^ s‖ ≤ P :=
    norm_positive_cpow_le_of_abs_re Real.pi_pos (abs_le.mpr ⟨by dsimp [B]; linarith, by dsimp [B]; linarith⟩)
  have hq : ‖(4 * Real.pi : ℂ) ^ (s + (k : ℂ) - 1)‖ ≤ Q := by
    have hh := norm_positive_cpow_le_of_abs_re (show (0 : ℝ) < 4 * Real.pi by positivity)
      (s := s + (k : ℂ) - 1) (B := B) (by
        simp only [sub_re, add_re, intCast_re, one_re]
        exact abs_le.mpr ⟨by dsimp [B]; linarith, by dsimp [B]; linarith⟩)
    simpa only [ofReal_mul, ofReal_ofNat] using hh
  have hg1 : ‖(Gamma (s + 1))⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := by
    have hh := norm_inv_Gamma_strip_le (B := B) (u := s.re + 1) (t := s.im)
      (by linarith) (by dsimp [B]; linarith) ht
    have he : gammaVerticalPoint (s.re + 1) s.im = s + 1 := by
      apply Complex.ext <;> simp [gammaVerticalPoint]
    simpa only [he] using hh
  have hg2 : ‖(Gamma (s + (k : ℂ) - 1))⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := by
    have hh := norm_inv_Gamma_strip_le (B := B) (u := s.re + k - 1) (t := s.im)
      (by linarith) (by dsimp [B]; linarith) ht
    have he : gammaVerticalPoint (s.re + k - 1) s.im = s + (k : ℂ) - 1 := by
      apply Complex.ext <;> simp [gammaVerticalPoint]
    simpa only [he] using hh
  rw [rankinConvolutionInverseFactor, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ P * Q * (G * Real.exp (Real.pi * |s.im|)) * (G * Real.exp (Real.pi * |s.im|)) := by
      gcongr
    _ = P * Q * G ^ 2 * (Real.exp (Real.pi * |s.im|) * Real.exp (Real.pi * |s.im|)) := by ring
    _ = _ := by
      rw [show 2 * Real.pi * |s.im| = Real.pi * |s.im| + Real.pi * |s.im| by ring, Real.exp_add]

/-- The actual entire Rankin pole numerator has a uniform polynomial times exponential bound on the contour strip. -/
theorem exists_rankinConvolutionEntireNumerator_strip_exponential {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 → 1 ≤ |s.im| →
      ‖rankinConvolutionEntireNumerator f s‖ ≤
        C * (1 + ‖s‖) ^ 2 * Real.exp (2 * Real.pi * |s.im|) := by
  obtain ⟨A, hA, hAb⟩ := exists_gamma0CuspEntire_strip_bound f (show (1 : ℝ) < 9 / 8 by norm_num)
  obtain ⟨B, hB, hBb⟩ := exists_rankinConvolutionInverseFactor_strip_bound hk
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro s hl hr ht
  rw [rankinConvolutionEntireNumerator, norm_mul]
  have hh := mul_le_mul (hAb s hr (by linarith)) (hBb s hl hr ht)
    (norm_nonneg _) (by positivity)
  convert hh using 1
  ring

end
end Dubon2026

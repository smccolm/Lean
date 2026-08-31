import GafniTao.FordCotangentPositivity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Order.Filter.AtTopBot.Group

/-!
# Ford's corrected cotangent function

Ford's zero inequality uses the holomorphic correction

`cot z - 1 / z + 4 z / pi^2`.

On the imaginary diameter of the right half-disc its real part is zero.  On
the circular arc of radius `pi / 2`, the rational correction has zero real
part, leaving the nonnegative real part of `cot`.  These are the exact two
boundary calculations in Ford's Lemma `cot`.
-/

open Complex Set

namespace GafniTao

noncomputable def fordCotangentCorrection (z : ℂ) : ℂ :=
  Complex.cot z - 1 / z + ((4 : ℝ) : ℂ) * z / (Real.pi : ℂ) ^ 2

private theorem div_pi_mem_integerComplement
    {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ Real.pi / 2) :
    z / (Real.pi : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hzEq : z = (Real.pi : ℂ) * n := by
    calc
      z = (Real.pi : ℂ) * (z / (Real.pi : ℂ)) := by field_simp
      _ = (Real.pi : ℂ) * n := by rw [← hn]
  have hnNorm : ‖(n : ℂ)‖ ≤ (1 : ℝ) / 2 := by
    rw [hzEq, norm_mul] at hz
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos] at hz
    nlinarith [Real.pi_pos]
  have hnAbs : |(n : ℝ)| ≤ (1 : ℝ) / 2 := by simpa using hnNorm
  have hnZero : n = 0 := by
    by_contra hn0
    have hone : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn0
    linarith
  exact hz0 (by simp [hzEq, hnZero])

private noncomputable def fordCotangentSeriesTerm (z : ℂ) (n : ℕ) : ℂ :=
  2 * z / (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2)

private theorem cotTerm_div_pi_eq
    {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ Real.pi / 2) (n : ℕ) :
    cotTerm (z / (Real.pi : ℂ)) n =
      (Real.pi : ℂ) * fordCotangentSeriesTerm z n := by
  have hx := div_pi_mem_integerComplement hz0 hz
  rw [cotTerm_identity hx]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hnPlus : z / (Real.pi : ℂ) + (n + 1 : ℕ) ≠ 0 := by
    simpa using Complex.integerComplement_add_ne_zero hx ((n : ℤ) + 1)
  have hnMinus : z / (Real.pi : ℂ) - (n + 1 : ℕ) ≠ 0 := by
    simpa [sub_eq_add_neg] using
      Complex.integerComplement_add_ne_zero hx (-(n + 1 : ℤ))
  rw [fordCotangentSeriesTerm]
  field_simp
  ring

private theorem summable_fordCotangentSeriesTerm
    {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ Real.pi / 2) :
    Summable (fordCotangentSeriesTerm z) := by
  have hx := div_pi_mem_integerComplement hz0 hz
  have hs := (summable_cotTerm hx).mul_left ((Real.pi : ℂ)⁻¹)
  refine hs.congr ?_
  intro n
  rw [cotTerm_div_pi_eq hz0 hz n]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

private theorem cot_sub_inv_eq_tsum_fordCotangentSeriesTerm
    {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ Real.pi / 2) :
    Complex.cot z - 1 / z = ∑' n : ℕ, fordCotangentSeriesTerm z n := by
  have hx := div_pi_mem_integerComplement hz0 hz
  have hseries := cot_series_rep' hx
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hscaled :
      (∑' n : ℕ, cotTerm (z / (Real.pi : ℂ)) n) =
        (Real.pi : ℂ) * ∑' n : ℕ, fordCotangentSeriesTerm z n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    exact fun n ↦ cotTerm_div_pi_eq hz0 hz n
  rw [hscaled] at hseries
  have hpiz : (Real.pi : ℂ) * (z / (Real.pi : ℂ)) = z := by field_simp
  rw [hpiz] at hseries
  have hinvScale : 1 / (z / (Real.pi : ℂ)) = (Real.pi : ℂ) / z := by
    field_simp
  rw [hinvScale] at hseries
  apply (mul_left_cancel₀ hpi)
  simpa [mul_sub, div_eq_mul_inv] using hseries

private noncomputable def fordCotangentMajorantTerm (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ 2 - 1 / 4)

private theorem fordCotangentMajorantTerm_eq_telescope (n : ℕ) :
    fordCotangentMajorantTerm n =
      1 / ((n : ℝ) + 1 / 2) - 1 / ((n : ℝ) + 3 / 2) := by
  have h₁ : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
  have h₂ : (n : ℝ) + 3 / 2 ≠ 0 := by positivity
  rw [fordCotangentMajorantTerm]
  rw [show ((n : ℝ) + 1) ^ 2 - 1 / 4 =
      ((n : ℝ) + 1 / 2) * ((n : ℝ) + 3 / 2) by ring]
  field_simp [h₁, h₂]
  ring

private theorem sum_fordCotangentMajorantTerm (N : ℕ) :
    ∑ n ∈ Finset.range N, fordCotangentMajorantTerm n =
      2 - 1 / ((N : ℝ) + 1 / 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, fordCotangentMajorantTerm_eq_telescope]
      push_cast
      ring

private theorem hasSum_fordCotangentMajorantTerm :
    HasSum fordCotangentMajorantTerm 2 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · simp only [sum_fordCotangentMajorantTerm]
    convert (tendsto_const_nhds (x := (2 : ℝ))).sub
        ((Filter.tendsto_atTop_add_const_right Filter.atTop (1 / 2 : ℝ)
          tendsto_natCast_atTop_atTop).inv_tendsto_atTop) using 1 <;>
      simp [one_div]
  · intro n
    rw [fordCotangentMajorantTerm]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdenom : 0 < ((n : ℝ) + 1) ^ 2 - 1 / 4 := by nlinarith
    exact one_div_nonneg.mpr hdenom.le

private theorem tsum_fordCotangentMajorantTerm :
    ∑' n : ℕ, fordCotangentMajorantTerm n = 2 :=
  hasSum_fordCotangentMajorantTerm.tsum_eq

private theorem fordCotangentSeriesTerm_re (z : ℂ) (n : ℕ) :
    (fordCotangentSeriesTerm z n).re =
      -(2 * z.re *
        (((Real.pi * ((n : ℝ) + 1)) ^ 2) - Complex.normSq z) /
        Complex.normSq
          (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2)) := by
  let a : ℝ := Real.pi * ((n : ℝ) + 1)
  have ha : ((Real.pi : ℂ) * (n + 1)) ^ 2 = (a ^ 2 : ℝ) := by
    apply Complex.ext <;> norm_num [a]
  have hwre :
      (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2).re =
        z.re ^ 2 - z.im ^ 2 - a ^ 2 := by
    rw [ha]
    simp [pow_two, Complex.mul_re]
  have hwim :
      (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2).im =
        2 * z.re * z.im := by
    rw [ha]
    simp [pow_two, Complex.mul_im]
    ring
  have hnumre : (2 * z).re = 2 * z.re := by norm_num
  have hnumim : (2 * z).im = 2 * z.im := by norm_num
  have hnorm : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq, pow_two]
  rw [fordCotangentSeriesTerm, Complex.div_re, hwre, hwim,
    hnumre, hnumim, hnorm]
  change _ = -(2 * z.re * (a ^ 2 - (z.re ^ 2 + z.im ^ 2)) / _)
  ring

private theorem fordCotangentSeriesDenom_normSq (z : ℂ) (n : ℕ) :
    Complex.normSq
        (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2) =
      (((Real.pi * ((n : ℝ) + 1)) ^ 2) - Complex.normSq z) ^ 2 +
        4 * (Real.pi * ((n : ℝ) + 1)) ^ 2 * z.im ^ 2 := by
  let a : ℝ := Real.pi * ((n : ℝ) + 1)
  have ha : ((Real.pi : ℂ) * (n + 1)) ^ 2 = (a ^ 2 : ℝ) := by
    apply Complex.ext <;> norm_num [a]
  have hwre :
      (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2).re =
        z.re ^ 2 - z.im ^ 2 - a ^ 2 := by
    rw [ha]
    simp [pow_two, Complex.mul_re]
  have hwim :
      (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2).im =
        2 * z.re * z.im := by
    rw [ha]
    simp [pow_two, Complex.mul_im]
    ring
  have hnorm : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq, pow_two]
  rw [show Complex.normSq
      (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2) =
      (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2).re ^ 2 +
        (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2).im ^ 2 by
          simp [Complex.normSq, pow_two],
    hwre, hwim, hnorm]
  change _ = (a ^ 2 - (z.re ^ 2 + z.im ^ 2)) ^ 2 +
    4 * a ^ 2 * z.im ^ 2
  ring

private theorem fordCotangentSeriesTerm_re_add_majorant_nonneg
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : ‖z‖ ≤ Real.pi / 2) (n : ℕ) :
    0 ≤ (fordCotangentSeriesTerm z n).re +
      (2 / Real.pi ^ 2 * fordCotangentMajorantTerm n) * z.re := by
  let a2 : ℝ := (Real.pi * ((n : ℝ) + 1)) ^ 2
  let r2 : ℝ := Complex.normSq z
  let c : ℝ := a2 - Real.pi ^ 2 / 4
  let b : ℝ := a2 - r2
  let d : ℝ := Complex.normSq
    (z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2)
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hnormSq : r2 ≤ Real.pi ^ 2 / 4 := by
    dsimp [r2]
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z, Real.pi_pos]
  have hm : 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have ha2 : Real.pi ^ 2 ≤ a2 := by
    dsimp [a2]
    nlinarith [sq_nonneg (Real.pi * ((n : ℝ) + 1) - Real.pi),
      Real.pi_pos]
  have hc : 0 < c := by
    dsimp [c]
    nlinarith
  have hbc : c ≤ b := by
    dsimp [b, c]
    linarith
  have hb : 0 < b := lt_of_lt_of_le hc hbc
  have hdFormula : d = b ^ 2 + 4 * a2 * z.im ^ 2 := by
    dsimp [d, b, a2, r2]
    rw [fordCotangentSeriesDenom_normSq]
  have ha2nonneg : 0 ≤ a2 := le_trans (sq_nonneg Real.pi) ha2
  have hdLower : b ^ 2 ≤ d := by
    rw [hdFormula]
    nlinarith [mul_nonneg ha2nonneg (sq_nonneg z.im)]
  have hd : 0 < d := lt_of_lt_of_le (sq_pos_of_pos hb) hdLower
  have hbcMul : b * c ≤ d := by
    calc
      b * c ≤ b * b := mul_le_mul_of_nonneg_left hbc hb.le
      _ = b ^ 2 := by ring
      _ ≤ d := hdLower
  have hfrac : b / d ≤ 1 / c := by
    exact (div_le_div_iff₀ hd hc).2 (by simpa using hbcMul)
  have hscaled : 2 * z.re * (b / d) ≤ 2 * z.re * (1 / c) :=
    mul_le_mul_of_nonneg_left hfrac (mul_nonneg (by norm_num) hzre)
  have hcFormula :
      c = Real.pi ^ 2 * (((n : ℝ) + 1) ^ 2 - 1 / 4) := by
    dsimp [c, a2]
    ring
  have hmajorant :
      2 / Real.pi ^ 2 * fordCotangentMajorantTerm n = 2 / c := by
    rw [fordCotangentMajorantTerm, hcFormula]
    field_simp [ne_of_gt hpi2, ne_of_gt hc]
  rw [fordCotangentSeriesTerm_re, hmajorant]
  change 0 ≤ -(2 * z.re * b / d) + (2 / c) * z.re
  have hscaled' : 2 * z.re * b / d ≤ 2 * z.re / c := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  calc
    0 ≤ 2 * z.re / c - 2 * z.re * b / d := sub_nonneg.mpr hscaled'
    _ = -(2 * z.re * b / d) + (2 / c) * z.re := by ring

/-- Ford's corrected-cotangent positivity lemma on the closed right half-disc.

This is the full conclusion of Ford's `lem:cot`, not merely its two boundary
calculations.  The proof uses the Mittag-Leffler expansion and the exact
telescoping sum `∑_{m≥1} (m² - 1/4)⁻¹ = 2`.
-/
theorem ford_cotangent_correction_nonneg
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : ‖z‖ ≤ Real.pi / 2) :
    0 ≤ (fordCotangentCorrection z).re := by
  by_cases hz0 : z = 0
  · subst z
    simp [fordCotangentCorrection, Complex.cot]
  have hs := summable_fordCotangentSeriesTerm hz0 hz
  have hsRe : Summable (fun n => (fordCotangentSeriesTerm z n).re) := by
    simpa only [Function.comp_apply, Complex.reCLM_apply] using
      hs.map Complex.reCLM Complex.reCLM.continuous
  have hmScaled :
      HasSum
        (fun n => (2 / Real.pi ^ 2 * fordCotangentMajorantTerm n) * z.re)
        (4 / Real.pi ^ 2 * z.re) := by
    have h := hasSum_fordCotangentMajorantTerm.mul_left
      (2 / Real.pi ^ 2 * z.re)
    convert h using 1
    · funext n
      ring
    · ring
  have hsumEq :
      (∑' n : ℕ, ((fordCotangentSeriesTerm z n).re +
          (2 / Real.pi ^ 2 * fordCotangentMajorantTerm n) * z.re)) =
        (∑' n : ℕ, (fordCotangentSeriesTerm z n).re) +
          4 / Real.pi ^ 2 * z.re :=
    (hsRe.hasSum.add hmScaled).tsum_eq
  have hsumNonneg :
      0 ≤ (∑' n : ℕ, ((fordCotangentSeriesTerm z n).re +
        (2 / Real.pi ^ 2 * fordCotangentMajorantTerm n) * z.re)) :=
    tsum_nonneg (fordCotangentSeriesTerm_re_add_majorant_nonneg hzre hz)
  rw [hsumEq] at hsumNonneg
  have hmap := Complex.reCLM.map_tsum hs
  change (∑' n : ℕ, fordCotangentSeriesTerm z n).re =
    ∑' n : ℕ, (fordCotangentSeriesTerm z n).re at hmap
  have hcotRe :
      (Complex.cot z - 1 / z).re =
        ∑' n : ℕ, (fordCotangentSeriesTerm z n).re := by
    rw [cot_sub_inv_eq_tsum_fordCotangentSeriesTerm hz0 hz]
    exact hmap
  have hlinear :
      ((((4 : ℝ) : ℂ) * z / (Real.pi : ℂ) ^ 2).re) =
        4 / Real.pi ^ 2 * z.re := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hpiPow : (Real.pi : ℂ) ^ 2 = (Real.pi ^ 2 : ℝ) := by
      norm_num
    rw [hpiPow, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    norm_num [Complex.normSq_ofReal]
    field_simp [hpi]
  rw [fordCotangentCorrection, Complex.add_re, hcotRe, hlinear]
  exact hsumNonneg

/-- The scaled form used when Ford discards the zeros in the detector disc.
It keeps the exact loss `Re z / eta²` generated by the correction term. -/
theorem fordCotKernel_sub_inv_re_lower
    {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hzre : 0 ≤ z.re) (hznorm : ‖z‖ ≤ eta) :
    -(z.re / eta ^ 2) ≤ (fordCotKernel eta z - 1 / z).re := by
  by_cases hz0 : z = 0
  · subst z
    simp [fordCotKernel, Complex.cot]
  let c : ℝ := Real.pi / (2 * eta)
  have hc : 0 < c := div_pos Real.pi_pos (mul_pos two_pos heta)
  have hscaledRe : 0 ≤ (((c : ℂ) * z).re) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg hc.le hzre
  have hscaledNorm : ‖(c : ℂ) * z‖ ≤ Real.pi / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    calc
      c * ‖z‖ ≤ c * eta := mul_le_mul_of_nonneg_left hznorm hc.le
      _ = Real.pi / 2 := by
        dsimp [c]
        field_simp [heta.ne']
  have hcorr := ford_cotangent_correction_nonneg hscaledRe hscaledNorm
  have hidentity :
      ((c : ℂ) * fordCotangentCorrection ((c : ℂ) * z)) =
        fordCotKernel eta z - 1 / z + z / (eta : ℂ) ^ 2 := by
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
    rw [fordCotangentCorrection, fordCotKernel]
    change (c : ℂ) *
        (Complex.cot ((c : ℂ) * z) - 1 / ((c : ℂ) * z) +
          (4 : ℂ) * ((c : ℂ) * z) / (Real.pi : ℂ) ^ 2) =
      (c : ℂ) * Complex.cot ((c : ℂ) * z) - 1 / z +
        z / (eta : ℂ) ^ 2
    have hinvScaled :
        (c : ℂ) * (1 / ((c : ℂ) * z)) = 1 / z := by
      field_simp [hc0, hz0]
    have hcorrectionScaled :
        (c : ℂ) *
            ((4 : ℂ) * ((c : ℂ) * z) / (Real.pi : ℂ) ^ 2) =
          z / (eta : ℂ) ^ 2 := by
      have hcFormula : 4 * c ^ 2 * eta ^ 2 = Real.pi ^ 2 := by
        dsimp [c]
        field_simp [heta.ne']
        ring
      have hcFormulaC :
          (4 : ℂ) * (c : ℂ) ^ 2 * (eta : ℂ) ^ 2 =
            (Real.pi : ℂ) ^ 2 := by
        exact_mod_cast hcFormula
      field_simp [hetaC, Real.pi_ne_zero]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcFormulaC
    rw [mul_add, mul_sub, hinvScaled, hcorrectionScaled]
  have hleft :
      0 ≤ (((c : ℂ) * fordCotangentCorrection ((c : ℂ) * z)).re) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hc.le hcorr
  have hlinearRe :
      (z / (eta : ℂ) ^ 2).re = z.re / eta ^ 2 := by
    have hetaPow : (eta : ℂ) ^ 2 = (eta ^ 2 : ℝ) := by norm_num
    rw [hetaPow]
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    norm_num [Complex.normSq_ofReal]
    field_simp [heta.ne']
  rw [hidentity, Complex.add_re, hlinearRe] at hleft
  linarith

theorem fordCotangentCorrection_re_imaginary (y : ℝ) :
    (fordCotangentCorrection ((y : ℂ) * Complex.I)).re = 0 := by
  have hpiPow : (Real.pi : ℂ) ^ 2 = (Real.pi ^ 2 : ℝ) := by
    norm_num
  have hcot : (Complex.cot ((y : ℂ) * Complex.I)).re = 0 := by
    rw [Complex.cot,
      show Complex.cos ((y : ℂ) * Complex.I) = Real.cosh y by
        simpa using Complex.cos_mul_I (y : ℂ),
      show Complex.sin ((y : ℂ) * Complex.I) =
          (Real.sinh y : ℂ) * Complex.I by
        simpa using Complex.sin_mul_I (y : ℂ),
      Complex.div_re]
    simp
  have hinv : ((1 : ℂ) / ((y : ℂ) * Complex.I)).re = 0 := by
    rw [Complex.div_re]
    simp
  have hlinear :
      ((((4 : ℝ) : ℂ) * ((y : ℂ) * Complex.I) /
          (Real.pi : ℂ) ^ 2).re) = 0 := by
    rw [hpiPow, Complex.div_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul,
      zero_div, add_zero]
  rw [fordCotangentCorrection, Complex.add_re, Complex.sub_re, hcot, hinv]
  change 0 - 0 +
      ((((4 : ℝ) : ℂ) * ((y : ℂ) * Complex.I) /
        (Real.pi : ℂ) ^ 2).re) = 0
  rw [hlinear]
  ring

theorem fordCotangentCorrection_re_eq_cot_re_of_norm
    {z : ℂ} (hz : ‖z‖ = Real.pi / 2) :
    (fordCotangentCorrection z).re = (Complex.cot z).re := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hnormSq : Complex.normSq z = Real.pi ^ 2 / 4 := by
    rw [← Complex.sq_norm]
    rw [hz]
    ring
  have hinv : ((1 : ℂ) / z).re = 4 * z.re / Real.pi ^ 2 := by
    rw [Complex.div_re, hnormSq]
    simp
    field_simp [hpi]
  have hlinear :
      ((((4 : ℝ) : ℂ) * z / (Real.pi : ℂ) ^ 2).re) =
        4 * z.re / Real.pi ^ 2 := by
    have hpiPow : (Real.pi : ℂ) ^ 2 = (Real.pi ^ 2 : ℝ) := by
      norm_num
    rw [hpiPow]
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    norm_num [Complex.normSq_ofReal]
    field_simp [hpi]
  simp only [fordCotangentCorrection, Complex.sub_re, Complex.add_re,
    hinv, hlinear]
  ring

theorem fordCotangentCorrection_re_nonneg_on_arc
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : ‖z‖ = Real.pi / 2) :
    0 ≤ (fordCotangentCorrection z).re := by
  rw [fordCotangentCorrection_re_eq_cot_re_of_norm hz]
  have hzreUpper : z.re ≤ Real.pi / 2 := by
    calc
      z.re ≤ |z.re| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
      _ = Real.pi / 2 := hz
  simpa [Complex.eta] using
    (ford_re_cot_nonneg (x := z.re) (y := z.im) hzre hzreUpper)

/-- Uniform norm majorant for one term in the Mittag--Leffler expansion of
`cot z - 1 / z` on Ford's closed half-disc.  Keeping this estimate explicit
is useful at the central pole of the zero detector: it proves removability,
not merely the value of the residue. -/
private theorem norm_fordCotangentSeriesTerm_le
    {z : ℂ} (hz : ‖z‖ ≤ Real.pi / 2) (n : ℕ) :
    ‖fordCotangentSeriesTerm z n‖ ≤
      (2 / Real.pi ^ 2 * fordCotangentMajorantTerm n) * ‖z‖ := by
  let a : ℝ := Real.pi * ((n : ℝ) + 1)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn : 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hzsq : ‖z ^ 2‖ ≤ Real.pi ^ 2 / 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have hnNorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, RCLike.norm_natCast]
    norm_num
  have haNorm : ‖((Real.pi : ℂ) * (n + 1)) ^ 2‖ = a ^ 2 := by
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpi, hnNorm]
  have hdenomLower :
      Real.pi ^ 2 * (((n : ℝ) + 1) ^ 2 - 1 / 4) ≤
        ‖z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2‖ := by
    have hrev := norm_sub_norm_le
      (((Real.pi : ℂ) * (n + 1)) ^ 2) (z ^ 2)
    rw [haNorm] at hrev
    have haFormula : a ^ 2 = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      dsimp [a]
      ring
    rw [haFormula] at hrev
    calc
      Real.pi ^ 2 * (((n : ℝ) + 1) ^ 2 - 1 / 4)
          = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 - Real.pi ^ 2 / 4 := by ring
      _ ≤ Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 - ‖z ^ 2‖ := by linarith
      _ ≤ ‖((Real.pi : ℂ) * (n + 1)) ^ 2 - z ^ 2‖ := by
        simpa [haFormula] using hrev
      _ = ‖z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2‖ := norm_sub_rev _ _
  have hfactorPos : 0 < ((n : ℝ) + 1) ^ 2 - 1 / 4 := by
    nlinarith
  have hdenomPos :
      0 < ‖z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2‖ :=
    lt_of_lt_of_le (mul_pos (sq_pos_of_pos hpi) hfactorPos) hdenomLower
  have hmajorantEq :
      2 / Real.pi ^ 2 * fordCotangentMajorantTerm n =
        2 / (Real.pi ^ 2 * (((n : ℝ) + 1) ^ 2 - 1 / 4)) := by
    rw [fordCotangentMajorantTerm]
    field_simp [Real.pi_ne_zero, ne_of_gt hfactorPos]
  rw [fordCotangentSeriesTerm, norm_div, norm_mul]
  simp only [norm_ofNat, hmajorantEq]
  have hnum : 0 ≤ 2 * ‖z‖ := mul_nonneg (by norm_num) (norm_nonneg z)
  have hbasePos :
      0 < Real.pi ^ 2 * (((n : ℝ) + 1) ^ 2 - 1 / 4) :=
    mul_pos (sq_pos_of_pos hpi) hfactorPos
  have hfrac :
      2 * ‖z‖ /
          ‖z ^ 2 - ((Real.pi : ℂ) * (n + 1)) ^ 2‖ ≤
        2 * ‖z‖ /
          (Real.pi ^ 2 * (((n : ℝ) + 1) ^ 2 - 1 / 4)) :=
    div_le_div_of_nonneg_left hnum hbasePos hdenomLower
  convert hfrac using 1
  all_goals ring

/-- The corrected cotangent is Lipschitz at the origin on Ford's half-disc.
In particular the apparent pole in `cot z - 1/z` is genuinely removable in
the Lean model. -/
theorem norm_fordCotangentCorrection_le
    {z : ℂ} (hz : ‖z‖ ≤ Real.pi / 2) :
    ‖fordCotangentCorrection z‖ ≤ 8 / Real.pi ^ 2 * ‖z‖ := by
  by_cases hz0 : z = 0
  · subst z
    simp [fordCotangentCorrection, Complex.cot]
  have hs := summable_fordCotangentSeriesTerm hz0 hz
  have hseries := cot_sub_inv_eq_tsum_fordCotangentSeriesTerm hz0 hz
  have htermSummable : Summable (fun n : ℕ =>
      (2 / Real.pi ^ 2 * fordCotangentMajorantTerm n) * ‖z‖) := by
    have h := hasSum_fordCotangentMajorantTerm.mul_left
      (2 / Real.pi ^ 2 * ‖z‖)
    exact h.summable.congr (fun n => by ring)
  have hnormTsum :
      ‖∑' n : ℕ, fordCotangentSeriesTerm z n‖ ≤
        ∑' n : ℕ, (2 / Real.pi ^ 2 *
          fordCotangentMajorantTerm n) * ‖z‖ := by
    calc
      ‖∑' n : ℕ, fordCotangentSeriesTerm z n‖ ≤
          ∑' n : ℕ, ‖fordCotangentSeriesTerm z n‖ :=
        norm_tsum_le_tsum_norm hs.norm
      _ ≤ ∑' n : ℕ, (2 / Real.pi ^ 2 *
          fordCotangentMajorantTerm n) * ‖z‖ :=
        hs.norm.tsum_le_tsum (fun n => norm_fordCotangentSeriesTerm_le hz n)
          htermSummable
  have hmajorantSum :
      (∑' n : ℕ, (2 / Real.pi ^ 2 *
          fordCotangentMajorantTerm n) * ‖z‖) =
        4 / Real.pi ^ 2 * ‖z‖ := by
    have h := hasSum_fordCotangentMajorantTerm.mul_left
      (2 / Real.pi ^ 2 * ‖z‖)
    calc
      (∑' n : ℕ, (2 / Real.pi ^ 2 *
          fordCotangentMajorantTerm n) * ‖z‖) =
          ∑' n : ℕ, (2 / Real.pi ^ 2 * ‖z‖) *
            fordCotangentMajorantTerm n := by
        apply tsum_congr
        intro n
        ring
      _ = (2 / Real.pi ^ 2 * ‖z‖) * 2 := h.tsum_eq
      _ = 4 / Real.pi ^ 2 * ‖z‖ := by ring
  rw [hmajorantSum] at hnormTsum
  have hlinear :
      ‖(((4 : ℝ) : ℂ) * z / (Real.pi : ℂ) ^ 2)‖ =
        4 / Real.pi ^ 2 * ‖z‖ := by
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), norm_pow,
      abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero]
  rw [fordCotangentCorrection, hseries]
  calc
    ‖(∑' n : ℕ, fordCotangentSeriesTerm z n) +
        ((4 : ℝ) : ℂ) * z / (Real.pi : ℂ) ^ 2‖ ≤
      ‖∑' n : ℕ, fordCotangentSeriesTerm z n‖ +
        ‖((4 : ℝ) : ℂ) * z / (Real.pi : ℂ) ^ 2‖ := norm_add_le _ _
    _ ≤ 4 / Real.pi ^ 2 * ‖z‖ + 4 / Real.pi ^ 2 * ‖z‖ := by
      rw [hlinear]
      exact add_le_add hnormTsum le_rfl
    _ = 8 / Real.pi ^ 2 * ‖z‖ := by ring

/-- The removable extension of Ford's corrected cotangent is continuous at
the origin. -/
theorem continuousAt_fordCotangentCorrection_zero :
    ContinuousAt fordCotangentCorrection 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let C : ℝ := 8 / Real.pi ^ 2
  have hC : 0 < C := div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
  refine ⟨min (Real.pi / 2) (ε / C), lt_min (by positivity)
    (div_pos hε hC), ?_⟩
  intro z hz
  rw [dist_eq_norm, sub_zero] at hz
  have hzHalf : ‖z‖ ≤ Real.pi / 2 :=
    (le_of_lt hz).trans (min_le_left _ _)
  have hzEps : ‖z‖ < ε / C := by
    exact hz.trans_le (min_le_right _ _)
  have hbound := norm_fordCotangentCorrection_le hzHalf
  have hlt : C * ‖z‖ < ε := by
    simpa [mul_comm] using (lt_div_iff₀ hC).mp hzEps
  simpa [C, fordCotangentCorrection, Complex.cot] using
    lt_of_le_of_lt hbound hlt

/-- Exact scaling identity for the removable part of Ford's detector
kernel. -/
theorem fordCotKernel_sub_inv_eq
    {eta : ℝ} (heta : 0 < eta) (z : ℂ) :
    fordCotKernel eta z - 1 / z =
      ((Real.pi / (2 * eta) : ℝ) : ℂ) *
          fordCotangentCorrection
            ((((Real.pi / (2 * eta) : ℝ) : ℂ) * z)) -
        z / (eta : ℂ) ^ 2 := by
  by_cases hz0 : z = 0
  · subst z
    simp [fordCotKernel, fordCotangentCorrection, Complex.cot]
  let c : ℝ := Real.pi / (2 * eta)
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos Real.pi_pos (mul_pos two_pos heta)).ne'
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have hinvScaled :
      (c : ℂ) * (1 / ((c : ℂ) * z)) = 1 / z := by
    field_simp [hc0, hz0]
  have hcFormula : 4 * c ^ 2 * eta ^ 2 = Real.pi ^ 2 := by
    dsimp [c]
    field_simp [heta.ne']
    ring
  have hcFormulaC :
      (4 : ℂ) * (c : ℂ) ^ 2 * (eta : ℂ) ^ 2 =
        (Real.pi : ℂ) ^ 2 := by
    exact_mod_cast hcFormula
  have hcorrectionScaled :
      (c : ℂ) *
          ((4 : ℂ) * ((c : ℂ) * z) / (Real.pi : ℂ) ^ 2) =
        z / (eta : ℂ) ^ 2 := by
    field_simp [hetaC, Real.pi_ne_zero]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcFormulaC
  rw [fordCotangentCorrection, fordCotKernel]
  change (c : ℂ) * Complex.cot ((c : ℂ) * z) - 1 / z =
    (c : ℂ) *
        (Complex.cot ((c : ℂ) * z) - 1 / ((c : ℂ) * z) +
          (4 : ℂ) * ((c : ℂ) * z) / (Real.pi : ℂ) ^ 2) -
      z / (eta : ℂ) ^ 2
  rw [mul_add, mul_sub, hinvScaled, hcorrectionScaled]
  ring

/-- The pole-subtracted Ford kernel is continuous at its center. -/
theorem continuousAt_fordCotKernel_sub_inv_zero
    {eta : ℝ} (heta : 0 < eta) :
    ContinuousAt (fun z : ℂ => fordCotKernel eta z - 1 / z) 0 := by
  let c : ℂ := ((Real.pi / (2 * eta) : ℝ) : ℂ)
  have hlin : ContinuousAt (fun z : ℂ => c * z) 0 := by fun_prop
  have hcorr : ContinuousAt
      (fun z : ℂ => fordCotangentCorrection (c * z)) 0 := by
    exact continuousAt_fordCotangentCorrection_zero.comp_of_eq hlin (by simp)
  have hrhs : ContinuousAt
      (fun z : ℂ => c * fordCotangentCorrection (c * z) -
        z / (eta : ℂ) ^ 2) 0 := by
    fun_prop
  apply hrhs.congr_of_eventuallyEq
  filter_upwards with z
  simpa only [c] using fordCotKernel_sub_inv_eq heta z

/-- Boundedness form of removability, in the exact shape required by the
finite residue theorem at the detector center. -/
theorem fordCotKernel_sub_inv_isBigO_one
    {eta : ℝ} (heta : 0 < eta) :
    (fun z : ℂ => fordCotKernel eta z - 1 / z)
      =O[nhds (0 : ℂ)] (1 : ℂ → ℂ) :=
  (continuousAt_fordCotKernel_sub_inv_zero heta).isBigO_one ℂ

end GafniTao

import Dubon2026.PrimitiveNormalizedRecurrence
import Mathlib.Analysis.RCLike.Sqrt

/-! # Actual normalized local roots and the primitive Hecke polynomial

These roots are constructed from the genuine Fourier coefficient. Their
algebraic identities are proved; unit-modulus purity is not assumed in the
objects and is not asserted for cusp forms without its arithmetic proof.
-/

namespace Dubon2026

open Polynomial

noncomputable section

/-- The first explicitly constructed root of the normalized Hecke polynomial. -/
def satakeRootPlus (z : ℂ) : ℂ := (z + Complex.sqrt (z ^ 2 - 4)) / 2

/-- The second explicitly constructed root of the normalized Hecke polynomial. -/
def satakeRootMinus (z : ℂ) : ℂ := (z - Complex.sqrt (z ^ 2 - 4)) / 2

theorem satakeRoot_sum (z : ℂ) : satakeRootPlus z + satakeRootMinus z = z := by
  unfold satakeRootPlus satakeRootMinus
  ring

theorem satakeRoot_product (z : ℂ) : satakeRootPlus z * satakeRootMinus z = 1 := by
  have hs : Complex.sqrt (z ^ 2 - 4) ^ 2 = z ^ 2 - 4 := by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]
    norm_num
  unfold satakeRootPlus satakeRootMinus
  linear_combination -hs / 4

/-- The literal two local roots factor the normalized Hecke Euler polynomial at every complex argument. -/
theorem satakeRoot_euler_factor (z t : ℂ) :
    (1 - satakeRootPlus z * t) * (1 - satakeRootMinus z * t) = 1 - z * t + t ^ 2 := by
  have hs := satakeRoot_sum z
  have hp := satakeRoot_product z
  linear_combination -t * hs + t ^ 2 * hp

/-- The first actual local root satisfies the normalized Hecke quadratic. -/
theorem satakeRootPlus_quadratic (z : ℂ) : (satakeRootPlus z) ^ 2 - z * satakeRootPlus z + 1 = 0 := by
  have hs := satakeRoot_sum z
  have hp := satakeRoot_product z
  linear_combination satakeRootPlus z * hs - hp

/-- The second actual local root satisfies the same normalized Hecke quadratic. -/
theorem satakeRootMinus_quadratic (z : ℂ) : (satakeRootMinus z) ^ 2 - z * satakeRootMinus z + 1 = 0 := by
  have hs := satakeRoot_sum z
  have hp := satakeRoot_product z
  linear_combination satakeRootMinus z * hs - hp

/-- The unramified normalized local root attached to the actual primitive form. -/
def primitiveSatakePlus {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (p : ℕ) : ℂ :=
  satakeRootPlus (normalizedCuspCoefficients f.toCuspForm p)

/-- The complementary normalized local root attached to the same actual primitive form. -/
def primitiveSatakeMinus {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (p : ℕ) : ℂ :=
  satakeRootMinus (normalizedCuspCoefficients f.toCuspForm p)

/-- The constructed roots retain the actual Fourier coefficient as trace and determinant one. -/
theorem primitiveSatake_trace_det {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (p : ℕ) :
    primitiveSatakePlus f p + primitiveSatakeMinus f p = normalizedCuspCoefficients f.toCuspForm p ∧
      primitiveSatakePlus f p * primitiveSatakeMinus f p = 1 :=
  ⟨satakeRoot_sum _, satakeRoot_product _⟩

/-- A root of the actual real determinant-one quadratic in the Ramanujan interval lies on the unit circle. -/
theorem norm_eq_one_of_real_quadratic {x : ℝ} (hx : |x| ≤ 2) {z : ℂ}
    (hz : z ^ 2 - (x : ℂ) * z + 1 = 0) : ‖z‖ = 1 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.zero_re, zero_mul, sub_zero] at hr
  simp only [pow_two, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_im, Complex.zero_im, zero_mul, add_zero] at hi
  have hb := abs_le.mp hx
  have hx2 : x ^ 2 ≤ 4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2 - x) (by linarith : 0 ≤ 2 + x)]
  have hreal : 2 * z.re = x := by
    by_cases him : z.im = 0
    · rw [him] at hr
      have he : (2 * z.re - x) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * z.re - x)]
      nlinarith
    · have he : z.im * (2 * z.re - x) = 0 := by nlinarith [hi]
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left him)
  have hn : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg z]

/-- The coefficient bound gives unit modulus for the two genuinely constructed local roots. -/
theorem satakeRoot_norms_of_real_bound {z : ℂ} (hz : z.im = 0) (hb : ‖z‖ ≤ 2) :
    ‖satakeRootPlus z‖ = 1 ∧ ‖satakeRootMinus z‖ = 1 := by
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz)
  have hx : |z.re| ≤ 2 := (Complex.abs_re_le_norm z).trans hb
  constructor
  · apply norm_eq_one_of_real_quadratic hx
    simpa only [← he] using satakeRootPlus_quadratic z
  · apply norm_eq_one_of_real_quadratic hx
    simpa only [← he] using satakeRootMinus_quadratic z

/-- Unit modulus of both actual local roots yields the precise coefficient norm bound. -/
theorem norm_le_two_of_satakeRoot_norms {z : ℂ}
    (hp : ‖satakeRootPlus z‖ = 1) (hm : ‖satakeRootMinus z‖ = 1) : ‖z‖ ≤ 2 := by
  have he := norm_add_le (satakeRootPlus z) (satakeRootMinus z)
  simpa only [satakeRoot_sum, hp, hm, one_add_one_eq_two] using he

/-- The exact primitive-form normalization identifies Deligne's local bound with unit-modulus local roots; neither side is asserted unconditionally. -/
theorem primitiveSatake_unit_iff_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) :
    (‖primitiveSatakePlus f p‖ = 1 ∧ ‖primitiveSatakeMinus f p‖ = 1) ↔
      ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 := by
  constructor
  · rintro ⟨hplus, hminus⟩
    exact norm_le_two_of_satakeRoot_norms hplus hminus
  · intro hb
    exact satakeRoot_norms_of_real_bound
      (primitiveCuspForm_normalizedCoefficient_im f p (hp.coprime_iff_not_dvd.mpr hpQ)) hb

end
end Dubon2026

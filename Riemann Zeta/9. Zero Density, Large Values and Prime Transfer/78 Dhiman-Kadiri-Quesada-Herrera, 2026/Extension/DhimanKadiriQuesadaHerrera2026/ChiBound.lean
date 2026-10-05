import DhimanKadiriQuesadaHerrera2026.ChiConstants
import DhimanKadiriQuesadaHerrera2026.GammaStrip
import DhimanKadiriQuesadaHerrera2026.ChiGammaFactor

/-! # The source Lemma 6 bound for the actual chi factor

The proof combines exact Gamma anchors, the horizontal digamma estimate and the
principal-branch identity underlying Lemma 7. The printed constants are retained.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex
open scoped ComplexConjugate

/-- The rotated principal power has the exact signed exponential modulus. -/
theorem norm_cpow_two_pi_div_I (s : ℂ) :
    ‖(2 * (Real.pi : ℂ) / I) ^ (s - 1)‖ =
      (2 * Real.pi) ^ (s.re - 1) * Real.exp (Real.pi * s.im / 2) := by
  rw [cpow_two_pi_div_I, norm_mul, norm_exp]
  have hp : ‖(2 * (Real.pi : ℂ)) ^ (s - 1)‖ = (2 * Real.pi) ^ (s.re - 1) := by
    simpa only [ofReal_mul, ofReal_ofNat, sub_re, one_re] using
      norm_cpow_eq_rpow_re_of_pos Real.two_pi_pos (s - 1)
  rw [hp]
  congr 2
  simp only [mul_re, mul_im, div_re, div_im, neg_re, neg_im, ofReal_re,
    ofReal_im, I_re, I_im, sub_re, sub_im, one_re, one_im]
  norm_num
  ring

/-- Conjugation identifies the Gamma norm in chi with the positive-height strip norm. -/
theorem norm_Gamma_one_sub_sigma_height (σ t : ℝ) :
    ‖Gamma (1 - ((σ : ℂ) + (t : ℂ) * I))‖ =
      ‖Gamma (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have he : 1 - ((σ : ℂ) + (t : ℂ) * I) =
      conj (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I) := by
    simp only [map_add, conj_ofReal, map_mul, conj_I, ofReal_sub, ofReal_one, map_sub, map_one]
    ring
  rw [he, Gamma_conj, norm_conj]

/-- Triangle inequality in the exact gamma-factor identity. -/
theorem norm_chi_le_gamma_factor (σ t : ℝ) :
    ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      ‖Gamma (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ((2 * Real.pi) ^ (σ - 1) * Real.exp (Real.pi * t / 2)) *
          (1 + Real.exp (-Real.pi * t)) := by
  rw [← gamma_factor_mul_one_sub_exp, norm_mul, norm_mul,
    norm_Gamma_one_sub_sigma_height, norm_cpow_two_pi_div_I]
  have h := norm_sub_le (1 : ℂ) (exp ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * I) * I))
  rw [norm_one, norm_exp_pi_mul_I] at h
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add] at h ⊢
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The positive real powers in the Gamma factor give the exact source height scale. -/
theorem gamma_chi_power_identity {b t : ℝ} (hb : 0 < b) (ht : 0 < t) (σ : ℝ) :
    b * t ^ (2 * (1 - σ) - 1) * (b ^ (σ - 1)) ^ 2 =
      ((b / t) ^ (σ - 1 / 2)) ^ 2 := by
  rw [Real.div_rpow hb.le ht.le, div_pow,
    ← Real.rpow_natCast (b ^ (σ - 1)) 2, ← Real.rpow_mul hb.le,
    ← Real.rpow_natCast (b ^ (σ - 1 / 2)) 2, ← Real.rpow_mul hb.le,
    ← Real.rpow_natCast (t ^ (σ - 1 / 2)) 2, ← Real.rpow_mul ht.le]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * (1 - σ) - 1 = -((σ - 1 / 2) * 2) by ring, Real.rpow_neg ht.le]
  have he : b * b ^ ((σ - 1) * 2) = b ^ ((σ - 1 / 2) * 2) := by
    nth_rw 1 [← Real.rpow_one b]
    rw [← Real.rpow_add hb]
    congr 1
    ring
  calc
    _ = (b * b ^ ((σ - 1) * 2)) / t ^ ((σ - 1 / 2) * 2) := by ring
    _ = _ := by rw [he]

/-- The two exact exponential factors cancel at the actual physical height. -/
theorem gamma_chi_exponential_identity (t : ℝ) :
    Real.exp (-Real.pi * t) * Real.exp (Real.pi * t / 2) ^ 2 = 1 := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  norm_num
  ring

/-- The exact height scale and all explicit corrections bound the squared chi modulus. -/
theorem norm_chi_sq_le_explicit {σ t : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht : 1 / Real.pi ≤ t) :
    ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      ((2 * Real.pi / t) ^ (σ - 1 / 2)) ^ 2 * (1 + Real.exp (-Real.pi * t)) ^ 2 *
        Real.exp (1 / (6 * t)) * Real.exp (min (1 - σ) (σ - 1 / 2) / t) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hx : 1 - σ ∈ Set.Icc 0 (1 / 2 : ℝ) := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hg := norm_Gamma_strip_sq_le ht hx
  rw [show 1 / 2 - (1 - σ) = σ - 1 / 2 by ring] at hg
  have hs := pow_le_pow_left₀ (norm_nonneg _) (norm_chi_le_gamma_factor σ t) 2
  rw [mul_pow, mul_pow] at hs
  calc
    _ ≤ (‖Gamma (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        ((2 * Real.pi) ^ (σ - 1) * Real.exp (Real.pi * t / 2)) ^ 2) *
        (1 + Real.exp (-Real.pi * t)) ^ 2 := hs
    _ ≤ (2 * Real.pi * t ^ (2 * (1 - σ) - 1) * Real.exp (-Real.pi * t) *
        Real.exp (1 / (6 * t)) * Real.exp (min (1 - σ) (σ - 1 / 2) / t) *
        ((2 * Real.pi) ^ (σ - 1) * Real.exp (Real.pi * t / 2)) ^ 2) *
        (1 + Real.exp (-Real.pi * t)) ^ 2 := by
      gcongr
    _ = (2 * Real.pi * t ^ (2 * (1 - σ) - 1) * ((2 * Real.pi) ^ (σ - 1)) ^ 2) *
        (Real.exp (-Real.pi * t) * Real.exp (Real.pi * t / 2) ^ 2) *
        (1 + Real.exp (-Real.pi * t)) ^ 2 * Real.exp (1 / (6 * t)) *
        Real.exp (min (1 - σ) (σ - 1 / 2) / t) := by ring
    _ = _ := by rw [gamma_chi_power_identity Real.two_pi_pos htpos,
      gamma_chi_exponential_identity, mul_one]

/-- Source Lemma 6 at positive height, with the literal C₀ and its exact threshold dependence. -/
theorem norm_chi_le_chiC0_positive {σ t₀ t : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 1 / Real.pi ≤ t₀) (ht : t₀ ≤ t) :
    ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ chiC0 σ t₀ * (2 * Real.pi / t) ^ (σ - 1 / 2) := by
  have htpos : 0 < t₀ := lt_of_lt_of_le (by positivity) ht₀
  have hh : 0 < t := htpos.trans_le ht
  have he : 1 + Real.exp (-Real.pi * t) ≤ 1 + Real.exp (-Real.pi * t₀) := by
    have hn : -Real.pi * t ≤ -Real.pi * t₀ := by nlinarith [Real.pi_pos]
    exact add_le_add le_rfl (Real.exp_le_exp.mpr hn)
  have hs := norm_chi_sq_le_explicit hσ (ht₀.trans ht)
  have hb : ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (chiC0 σ t₀ * (2 * Real.pi / t) ^ (σ - 1 / 2)) ^ 2 := by
    calc
      _ ≤ ((2 * Real.pi / t) ^ (σ - 1 / 2)) ^ 2 * (1 + Real.exp (-Real.pi * t)) ^ 2 *
          Real.exp (1 / (6 * t)) * Real.exp (min (1 - σ) (σ - 1 / 2) / t) := hs
      _ ≤ ((2 * Real.pi / t) ^ (σ - 1 / 2)) ^ 2 * (1 + Real.exp (-Real.pi * t₀)) ^ 2 *
          chiC2 t₀ ^ 2 * (1 + chiC1 σ t₀ / t₀) ^ 2 := by
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) he 2)
            (sq_nonneg _)) (exp_gamma_anchor_le_chiC2_sq htpos ht)
              (Real.exp_pos _).le (by positivity))
          (exp_anchor_distance_sq_le hσ ht₀ ht) (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [chiC0_eq htpos]; ring
  have hn : 0 ≤ chiC0 σ t₀ * (2 * Real.pi / t) ^ (σ - 1 / 2) :=
    mul_nonneg (chiC0_pos hσ htpos).le (Real.rpow_nonneg (by positivity) _)
  nlinarith [norm_nonneg (chi ((σ : ℂ) + (t : ℂ) * I))]

/-- Conjugation makes the chi modulus even in its real height parameter. -/
theorem norm_chi_neg_height (σ t : ℝ) :
    ‖chi ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)‖ = ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ := by
  have he : (σ : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((σ : ℂ) + (t : ℂ) * I) := by simp
  rw [he, chi_conj, norm_conj]

/-- Source Lemma 6 on its full closed sigma interval and both signs of the height. -/
theorem norm_chi_le_chiC0 {σ t₀ t : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 1 / Real.pi ≤ t₀) (ht : t₀ ≤ |t|) :
    ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ chiC0 σ t₀ * (2 * Real.pi / |t|) ^ (σ - 1 / 2) := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact norm_chi_le_chiC0_positive hσ ht₀ ht
  · rw [abs_of_nonpos h] at ht ⊢
    have hb := norm_chi_le_chiC0_positive hσ ht₀ ht
    rwa [norm_chi_neg_height] at hb

end DhimanKadiriQuesadaHerrera2026

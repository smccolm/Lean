import DhimanKadiriQuesadaHerrera2026.Objects
import GuthMaynard.ZeroCount
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-! # Functional equation and conjugation for the actual AFE remainder

The zeta conjugation theorem is reused directly from the existing node-71 foundation.
The chi convention is the literal product in the paper, with principal complex powers.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex
open scoped BigOperators ComplexConjugate

/-- Combining the two positive real bases preserves the paper's chi convention. -/
theorem chi_eq_two_mul (s : ℂ) :
    chi s = 2 * (2 * (Real.pi : ℂ)) ^ (s - 1) * Gamma (1 - s) *
      sin ((Real.pi : ℂ) * s / 2) := by
  have hpow := mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    Real.pi_pos.le (s - 1)
  norm_num only [ofReal_ofNat] at hpow
  rw [hpow]
  have htwo : (2 : ℂ) ^ s = 2 * (2 : ℂ) ^ (s - 1) := by
    conv_lhs => rw [show s = s - 1 + 1 by ring]
    rw [cpow_add _ _ (by norm_num), cpow_one]
    ring
  simp only [chi, htwo]
  ring

/-- The functional equation in the orientation required by the paper's actual chi factor. -/
theorem zeta_eq_chi_mul_zeta_one_sub {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta s = chi s * riemannZeta (1 - s) := by
  have hne (n : ℕ) : 1 - s ≠ -(n : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im, one_im, neg_im, natCast_im] at hi
    exact hs (by linarith)
  have hne1 : 1 - s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im, one_im] at hi
    exact hs (by linarith)
  have h := riemannZeta_one_sub hne hne1
  rw [show 1 - (1 - s) = s by ring, show -(1 - s) = s - 1 by ring,
    show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 -
      (Real.pi : ℂ) * s / 2 by ring, cos_pi_div_two_sub] at h
  rw [chi_eq_two_mul]
  exact h

/-- Conjugation commutes with a principal power of a nonnegative real base. -/
theorem conj_nonneg_cpow {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    conj ((x : ℂ) ^ s) = (x : ℂ) ^ conj s := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hx]
    exact Real.pi_ne_zero.symm
  simpa only [conj_ofReal] using (cpow_conj (x : ℂ) s harg).symm

/-- The literal chi product commutes with conjugation. -/
theorem chi_conj (s : ℂ) : chi (conj s) = conj (chi s) := by
  have htwo := conj_nonneg_cpow (by norm_num : (0 : ℝ) ≤ 2) s
  have hpi := conj_nonneg_cpow Real.pi_pos.le (s - 1)
  norm_num only [ofReal_ofNat] at htwo
  simp only [chi, map_mul, htwo, hpi, map_sub, map_one, ← Gamma_conj,
    ← sin_conj, map_div₀, conj_ofReal, map_ofNat]

/-- Every positive-integer term has the required conjugation convention. -/
theorem zetaTerm_conj (s : ℂ) (n : ℕ) :
    zetaTerm (conj s) n = conj (zetaTerm s n) := by
  simpa only [zetaTerm, map_neg, ofReal_natCast] using
    (conj_nonneg_cpow (Nat.cast_nonneg n) (-s)).symm

/-- The sharp cutoff is unchanged under conjugation of the exponent. -/
theorem sharpZetaSum_conj (s : ℂ) (x : ℝ) :
    sharpZetaSum (conj s) x = conj (sharpZetaSum s x) := by
  simp only [sharpZetaSum, map_sum, zetaTerm_conj]

/-- Conjugation transports the actual two-polynomial remainder, away from the zeta pole. -/
theorem afeRemainder_conj {s : ℂ} (hs : s ≠ 1) (x y : ℝ) :
    afeRemainder (conj s) x y = conj (afeRemainder s x y) := by
  have hz := RiemannZeta.GuthMaynard.riemannZeta_conj s hs
  change riemannZeta (conj s) = conj (riemannZeta s) at hz
  have hsharp := sharpZetaSum_conj (1 - s) y
  simp only [map_sub, map_one] at hsharp
  simp only [afeRemainder, hz, sharpZetaSum_conj, chi_conj, map_sub, map_mul, hsharp]

/-- Positive and negative heights have the same actual AFE remainder norm. -/
theorem norm_afeRemainder_neg_height {σ t : ℝ} (ht : t ≠ 0) (x y : ℝ) :
    ‖afeRemainder ((σ : ℂ) - (t : ℂ) * I) x y‖ =
      ‖afeRemainder ((σ : ℂ) + (t : ℂ) * I) x y‖ := by
  have hs : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
      mul_zero, add_zero, zero_add, one_im] at hi
    exact ht hi
  have hc : conj ((σ : ℂ) + (t : ℂ) * I) = (σ : ℂ) - (t : ℂ) * I := by
    simp [sub_eq_add_neg]
  rw [← hc, afeRemainder_conj hs, norm_conj]

/-- Off the real axis, the sine denominator in gamma reflection is nonzero. -/
theorem sin_pi_mul_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    sin ((Real.pi : ℂ) * s) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro n h
  have hi := congrArg Complex.im h
  simp only [mul_im, ofReal_re, ofReal_im, intCast_im, intCast_re, mul_zero,
    zero_mul, add_zero] at hi
  exact hs ((mul_eq_zero.mp hi).resolve_left Real.pi_ne_zero)

/-- The two chi factors are reciprocal at every nonreal point. -/
theorem chi_mul_chi_one_sub {s : ℂ} (hs : s.im ≠ 0) :
    chi s * chi (1 - s) = 1 := by
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hbase : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hp
  have hpow : (2 * (Real.pi : ℂ)) ^ (s - 1) *
      (2 * (Real.pi : ℂ)) ^ (-s) = (2 * (Real.pi : ℂ))⁻¹ := by
    rw [← cpow_add _ _ hbase, show s - 1 + -s = -(1 : ℂ) by ring,
      cpow_neg, cpow_one]
  have htrig : 2 * sin ((Real.pi : ℂ) * s / 2) *
      cos ((Real.pi : ℂ) * s / 2) = sin ((Real.pi : ℂ) * s) := by
    rw [← sin_two_mul]
    congr 1
    ring
  rw [chi_eq_two_mul, chi_eq_two_mul,
    show 1 - s - 1 = -s by ring, show 1 - (1 - s) = s by ring,
    show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 -
      (Real.pi : ℂ) * s / 2 by ring, sin_pi_div_two_sub]
  calc
    _ = 2 * ((2 * (Real.pi : ℂ)) ^ (s - 1) * (2 * (Real.pi : ℂ)) ^ (-s)) *
        (Gamma s * Gamma (1 - s)) *
        (2 * sin ((Real.pi : ℂ) * s / 2) * cos ((Real.pi : ℂ) * s / 2)) := by ring
    _ = 1 := by
      rw [hpow, Gamma_mul_Gamma_one_sub, htrig]
      field_simp [hp, sin_pi_mul_ne_zero hs]

/-- Reflection exchanges the two actual Dirichlet polynomials and multiplies the remainder by chi. -/
theorem afeRemainder_reflection {s : ℂ} (hs : s.im ≠ 0) (x y : ℝ) :
    afeRemainder s x y = chi s * afeRemainder (1 - s) y x := by
  have hz := zeta_eq_chi_mul_zeta_one_sub hs
  have hc := chi_mul_chi_one_sub hs
  simp only [afeRemainder, show 1 - (1 - s) = s by ring]
  rw [hz]
  linear_combination sharpZetaSum s x * hc

/-- The reflected branch has exactly the chi norm as its multiplicative loss. -/
theorem norm_afeRemainder_reflection {s : ℂ} (hs : s.im ≠ 0) (x y : ℝ) :
    ‖afeRemainder s x y‖ = ‖chi s‖ * ‖afeRemainder (1 - s) y x‖ := by
  rw [afeRemainder_reflection hs, norm_mul]

/-- The critical-line chi factor has norm exactly one, including negative heights. -/
theorem norm_chi_critical_line {s : ℂ} (hre : s.re = 1 / 2) (him : s.im ≠ 0) :
    ‖chi s‖ = 1 := by
  have hc : 1 - s = conj s := by
    apply Complex.ext
    · simp only [sub_re, one_re, conj_re]
      linarith
    · simp only [sub_im, one_im, conj_im]
      ring
  have hn := congrArg norm (chi_mul_chi_one_sub him)
  rw [norm_mul, hc, chi_conj, norm_conj, norm_one] at hn
  nlinarith [norm_nonneg (chi s)]

end DhimanKadiriQuesadaHerrera2026

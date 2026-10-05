import DhimanKadiriQuesadaHerrera2026.GammaDigammaReal
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-! # Explicit horizontal comparison of the actual Gamma modulus

The squared-norm derivative calculation follows the existing node-74
`PintzGammaHorizontalSharp.lean` pattern (SHA-256
`0fc39e75ff81073d6f1788021f00c0a2bccef7ee1ea1949cfe5f5bb5fc40a2d4`).
The explicit digamma bound here also covers real part zero. The mean value theorem
is applied to the normalized logarithmic modulus, with no assumed Gamma bound.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex

/-- Positive height excludes every Gamma pole, including at real part zero. -/
theorem gamma_horizontal_ne_pole {t : ℝ} (ht : 0 < t) (x : ℝ) (n : ℕ) :
    (x : ℂ) + (t : ℂ) * I ≠ -(n : ℂ) := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

/-- The actual Gamma value is nonzero everywhere on the horizontal line. -/
theorem gamma_horizontal_ne_zero {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Gamma ((x : ℂ) + (t : ℂ) * I) ≠ 0 :=
  Gamma_ne_zero (gamma_horizontal_ne_pole ht x)

/-- The horizontal Gamma derivative is Gamma times its actual logarithmic derivative. -/
theorem gamma_horizontal_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun u : ℝ => Gamma ((u : ℂ) + (t : ℂ) * I))
      (Gamma ((x : ℂ) + (t : ℂ) * I) * digamma ((x : ℂ) + (t : ℂ) * I)) x := by
  have he : deriv Gamma ((x : ℂ) + (t : ℂ) * I) =
      Gamma ((x : ℂ) + (t : ℂ) * I) * digamma ((x : ℂ) + (t : ℂ) * I) := by
    rw [digamma_def, logDeriv_apply]
    field_simp [gamma_horizontal_ne_zero ht x]
  have hd := (differentiableAt_Gamma ((x : ℂ) + (t : ℂ) * I)
    (gamma_horizontal_ne_pole ht x)).hasDerivAt
  rw [he] at hd
  have hshift := (hasDerivAt_id (x : ℂ)).add_const ((t : ℂ) * I)
  simpa only [mul_one] using (hd.comp (x : ℂ) hshift).comp_ofReal

private theorem gamma_real_inner_self_mul (z w : ℂ) :
    inner ℝ z (z * w) = ‖z‖ ^ 2 * w.re := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  rw [show starRingEnd ℂ z * (z * w) = (starRingEnd ℂ z * z) * w by ring]
  rw [Complex.conj_mul']
  change (((↑‖z‖ : ℂ) ^ 2) * w).re = ‖z‖ ^ 2 * w.re
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- The logarithm of the Gamma modulus differentiates to the real part of digamma. -/
theorem log_norm_Gamma_horizontal_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.log ‖Gamma ((u : ℂ) + (t : ℂ) * I)‖)
      (digamma ((x : ℂ) + (t : ℂ) * I)).re x := by
  have hn : ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gamma_horizontal_ne_zero ht x)
  have hd := (((gamma_horizontal_hasDerivAt ht x).norm_sq).log (pow_ne_zero 2 hn)).div_const 2
  convert hd using 1
  · funext u
    rw [Real.log_pow]
    ring
  · rw [gamma_real_inner_self_mul]
    field_simp

/-- Remove the physical height power from the logarithm of the Gamma modulus. -/
noncomputable def gammaLogModulus (t x : ℝ) : ℝ :=
  Real.log ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ - x * Real.log t

/-- The derivative of the normalized modulus has the explicit digamma correction. -/
theorem gammaLogModulus_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (gammaLogModulus t)
      ((digamma ((x : ℂ) + (t : ℂ) * I)).re - Real.log t) x := by
  simpa only [one_mul] using (log_norm_Gamma_horizontal_hasDerivAt ht x).sub
    ((hasDerivAt_id x).mul_const (Real.log t))

/-- A uniform comparison between any two points of the closed Gamma segment. -/
theorem abs_gammaLogModulus_sub_le {t a x : ℝ} (ht : 0 < t)
    (ha : a ∈ Set.Icc 0 (1 / 2 : ℝ)) (hx : x ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    |gammaLogModulus t x - gammaLogModulus t a| ≤ |x - a| / (2 * t) := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ Set.Icc 0 (1 / 2 : ℝ)) => (gammaLogModulus_hasDerivAt ht u).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using abs_re_digamma_sub_log_height_le ht hu)
    (convex_Icc (0 : ℝ) (1 / 2)) ha hx
  simpa only [Real.norm_eq_abs, one_div, div_eq_mul_inv, mul_comm, one_mul] using h

/-- The explicit comparison retains the actual Gamma values and the exact height power. -/
theorem norm_Gamma_horizontal_le {t a x : ℝ} (ht : 0 < t)
    (ha : a ∈ Set.Icc 0 (1 / 2 : ℝ)) (hx : x ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ ≤
      ‖Gamma ((a : ℂ) + (t : ℂ) * I)‖ * t ^ (x - a) * Real.exp (|x - a| / (2 * t)) := by
  have h := (abs_le.mp (abs_gammaLogModulus_sub_le ht ha hx)).2
  dsimp only [gammaLogModulus] at h
  have hlog : Real.log ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ ≤
      Real.log ‖Gamma ((a : ℂ) + (t : ℂ) * I)‖ +
        Real.log t * (x - a) + |x - a| / (2 * t) := by nlinarith
  have hp (u : ℝ) : 0 < ‖Gamma ((u : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gamma_horizontal_ne_zero ht u)
  have he := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_add, Real.exp_add, Real.exp_log (hp x), Real.exp_log (hp a),
    ← Real.rpow_def_of_pos ht] at he

end DhimanKadiriQuesadaHerrera2026

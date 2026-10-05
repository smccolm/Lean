import DongWangWangZhang2026.RegularizedTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian identity with the zeta pole term retained

The regularized full-line transform is absolutely convergent in the strip.
Gaussian pairing restores the subtracted exponential as the exact positive residue.
-/

namespace DongWangWangZhang2026

open Complex MeasureTheory

noncomputable section

/-- Gaussian Fourier integral in the paper's unscaled frequency convention. -/
theorem integral_source_gaussian_phase (V u : ℝ) (hV : 0 < V) :
    (∫ ξ : ℝ, Complex.exp (((-ξ * u : ℝ) : ℂ) * I) *
      (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)) =
      (Real.sqrt (2 * Real.pi * V) : ℂ) * (Real.exp (-V * u ^ 2 / 2) : ℂ) := by
  have hb : 0 < ((1 / (2 * V) : ℝ) : ℂ).re := by simp; positivity
  have hroot : ((Real.pi : ℂ) / ((1 / (2 * V) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (2 * Real.pi * V) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1
    field_simp
  have hexp (ξ : ℝ) : (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ) =
      Complex.exp (-((1 / (2 * V) : ℝ) : ℂ) * (ξ : ℂ) ^ 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase (ξ : ℝ) : Complex.exp (((-ξ * u : ℝ) : ℂ) * I) =
      Complex.exp (I * (-(u : ℂ)) * ξ) := by congr 1; push_cast; ring
  simp_rw [hexp, hphase]
  rw [fourierIntegral_gaussian hb, hroot, Complex.ofReal_exp]
  congr 2
  push_cast
  field_simp
  ring

/-- The joint Gaussian Fourier integrand is absolutely integrable. -/
theorem integrable_source_gaussian_double {f : ℝ → ℂ} (hf : Integrable f)
    (V : ℝ) (hV : 0 < V) :
    Integrable (fun p : ℝ × ℝ =>
      f p.2 * Complex.exp (((-p.1 * p.2 : ℝ) : ℂ) * I) *
        (Real.exp (-p.1 ^ 2 / (2 * V)) : ℂ)) := by
  let g : ℝ → ℂ := fun ξ => (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)
  have hg : Integrable g := by
    have h : Integrable (fun ξ : ℝ => (Real.exp (-(1 / (2 * V)) * ξ ^ 2) : ℂ)) :=
      (integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (2 * V))).ofReal
    convert h using 1
    ext ξ
    dsimp only [g]
    congr 2
    ring
  have hdouble : Integrable (fun p : ℝ × ℝ =>
      f p.2 * Complex.exp (((-p.1 * p.2 : ℝ) : ℂ) * I) * g p.1) := by
    apply (hg.norm.mul_prod hf.norm).mono'
    · exact (hf.aestronglyMeasurable.comp_snd.mul
        (by fun_prop : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (((-p.1 * p.2 : ℝ) : ℂ) * I))).aestronglyMeasurable).mul
            hg.aestronglyMeasurable.comp_fst
    · filter_upwards with p
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact le_of_eq (mul_comm _ _)
  exact hdouble

/-- Absolute convergence of the Gaussian-weighted frequency transform. -/
theorem integrable_source_gaussian_frequency {f : ℝ → ℂ} (hf : Integrable f)
    (V : ℝ) (hV : 0 < V) :
    Integrable (fun ξ : ℝ =>
      (∫ u : ℝ, f u * Complex.exp (((-ξ * u : ℝ) : ℂ) * I)) *
        (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)) := by
  apply (integrable_source_gaussian_double hf V hV).integral_prod_left.congr
  filter_upwards with ξ
  exact integral_mul_const _ _

/-- Absolutely convergent Gaussian pairing, with both frequency and scale integrals actual. -/
theorem source_gaussian_pairing {f : ℝ → ℂ} (hf : Integrable f) (V : ℝ) (hV : 0 < V) :
    (Real.sqrt (2 * Real.pi * V) : ℂ) *
      (∫ u : ℝ, f u * (Real.exp (-V * u ^ 2 / 2) : ℂ)) =
    ∫ ξ : ℝ, (∫ u : ℝ, f u * Complex.exp (((-ξ * u : ℝ) : ℂ) * I)) *
      (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ) := by
  let g : ℝ → ℂ := fun ξ => (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)
  have hdouble := integrable_source_gaussian_double hf V hV
  calc
    _ = ∫ u : ℝ, f u * ∫ ξ : ℝ, Complex.exp (((-ξ * u : ℝ) : ℂ) * I) * g ξ := by
      simp_rw [g, integral_source_gaussian_phase V _ hV, ← mul_assoc,
        mul_comm (f _) (Real.sqrt (2 * Real.pi * V) : ℂ), mul_assoc]
      rw [integral_const_mul]
    _ = ∫ u : ℝ, ∫ ξ : ℝ, f u * Complex.exp (((-ξ * u : ℝ) : ℂ) * I) * g ξ := by
      simp_rw [← integral_const_mul, mul_assoc]
    _ = ∫ ξ : ℝ, ∫ u : ℝ, f u * Complex.exp (((-ξ * u : ℝ) : ℂ) * I) * g ξ :=
      (integral_integral_swap hdouble).symm
    _ = _ := by simp_rw [integral_mul_const]; rfl

/-- Gaussian pairing applied to the actual convergent remainder in the strip. -/
theorem regularized_source_gaussian_identity (a t V : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) :
    (Real.sqrt (2 * Real.pi * V) : ℂ) *
      (∫ u : ℝ, (zetaExpRemainder t u * Complex.exp (-((1 - a : ℝ) : ℂ) * u)) *
        (Real.exp (-V * u ^ 2 / 2) : ℂ)) =
      ∫ ξ : ℝ, (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
        (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)) *
          (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ) := by
  have hf := integrable_zetaExpRemainder t (s := ((1 - a : ℝ) : ℂ))
    (by simpa using sub_pos.mpr ha1) (by simpa using sub_lt_self 1 ha)
  rw [source_gaussian_pairing hf V hV]
  apply integral_congr_ae
  filter_upwards with ξ
  congr 1
  have h := integral_zetaExpRemainder t (s := ((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)
    (by simp; linarith) (by simp; linarith)
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with u
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · congr 2
    push_cast
    ring

/-- Absolute convergence of the actual zeta integral in Lemma 3.3. -/
theorem integrable_source_gaussian_zeta (a t V : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) :
    Integrable (fun ξ : ℝ =>
      (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
        (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)) *
          (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)) := by
  have hf := integrable_zetaExpRemainder t (s := ((1 - a : ℝ) : ℂ))
    (by simpa using sub_pos.mpr ha1) (by simpa using sub_lt_self 1 ha)
  apply (integrable_source_gaussian_frequency hf V hV).congr
  filter_upwards with ξ
  congr 1
  have h := integral_zetaExpRemainder t (s := ((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)
    (by simp; linarith) (by simp; linarith)
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with u
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · congr 2
    push_cast
    ring

/-- Absolute convergence of the Gaussian-smoothed remainder. -/
theorem integrable_source_gaussian_remainder (a t V : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) :
    Integrable (fun u : ℝ =>
      (zetaExpRemainder t u * Complex.exp (-((1 - a : ℝ) : ℂ) * u)) *
        (Real.exp (-V * u ^ 2 / 2) : ℂ)) := by
  apply (integrable_zetaExpRemainder t (s := ((1 - a : ℝ) : ℂ))
    (by simpa using sub_pos.mpr ha1) (by simpa using sub_lt_self 1 ha)).mul_bdd
    (by fun_prop) (c := 1)
  filter_upwards with u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ V * u ^ 2 / 2 := by positivity
  linarith

/-- Absolute convergence of the explicit term that restores the zeta pole. -/
theorem integrable_source_gaussian_pole (a t V : ℝ) (hV : 0 < V) :
    Integrable (fun u : ℝ =>
      Complex.exp (((a : ℂ) + (t : ℂ) * I) * u - (V : ℂ) * u ^ 2 / 2) /
        ((t : ℂ) * I + 1)) := by
  have h := (integrable_cexp_quadratic (b := (V : ℂ) / 2)
    (by simp; positivity) ((a : ℂ) + (t : ℂ) * I) 0).div_const ((t : ℂ) * I + 1)
  convert h using 1
  ext u
  congr 2
  ring

/-- The subtracted exponential gives exactly the positive source residue. -/
theorem integral_source_gaussian_pole (a t V : ℝ) (hV : 0 < V) :
    (Real.sqrt (2 * Real.pi * V) : ℂ) *
      (∫ u : ℝ, Complex.exp (((a : ℂ) + (t : ℂ) * I) * u - (V : ℂ) * u ^ 2 / 2) /
        ((t : ℂ) * I + 1)) =
      (2 * Real.pi : ℂ) / ((t : ℂ) * I + 1) *
        Complex.exp (((a : ℂ) + (t : ℂ) * I) ^ 2 / (2 * (V : ℂ))) := by
  have hb : (-(V : ℂ) / 2).re < 0 := by simp; linarith
  have hi := integral_cexp_quadratic hb ((a : ℂ) + (t : ℂ) * I) 0
  have hroot : ((Real.pi : ℂ) / (-(-(V : ℂ) / 2))) ^ (1 / 2 : ℂ) =
      (Real.sqrt (2 * Real.pi / V) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1
    field_simp
  have hroots : Real.sqrt (2 * Real.pi * V) * Real.sqrt (2 * Real.pi / V) =
      2 * Real.pi := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * Real.pi * V * (2 * Real.pi / V) = (2 * Real.pi) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
  have hform : (fun u : ℝ =>
      Complex.exp (((a : ℂ) + (t : ℂ) * I) * u - (V : ℂ) * u ^ 2 / 2)) =
      (fun u : ℝ => Complex.exp ((-(V : ℂ) / 2) * u ^ 2 +
        ((a : ℂ) + (t : ℂ) * I) * u + 0)) := by
    funext u
    congr 1
    ring
  rw [integral_div, hform, hi, hroot]
  have hexp : (0 : ℂ) - ((a : ℂ) + (t : ℂ) * I) ^ 2 / (4 * (-(V : ℂ) / 2)) =
      ((a : ℂ) + (t : ℂ) * I) ^ 2 / (2 * (V : ℂ)) := by ring
  rw [hexp]
  have hrootsC : (Real.sqrt (2 * Real.pi * V) : ℂ) *
      (Real.sqrt (2 * Real.pi / V) : ℂ) = (2 * Real.pi : ℂ) := by exact_mod_cast hroots
  calc
    _ = ((Real.sqrt (2 * Real.pi * V) : ℂ) * (Real.sqrt (2 * Real.pi / V) : ℂ)) /
        ((t : ℂ) * I + 1) * Complex.exp (((a : ℂ) + (t : ℂ) * I) ^ 2 /
          (2 * (V : ℂ))) := by ring
    _ = _ := by rw [hrootsC]

private theorem source_gaussian_sum_split (a t V u : ℝ) :
    zetaSum (Real.exp u) t * (Real.exp ((a - 1) * u - V * u ^ 2 / 2) : ℂ) =
      (zetaExpRemainder t u * Complex.exp (-((1 - a : ℝ) : ℂ) * u)) *
          (Real.exp (-V * u ^ 2 / 2) : ℂ) +
        Complex.exp (((a : ℂ) + (t : ℂ) * I) * u - (V : ℂ) * u ^ 2 / 2) /
          ((t : ℂ) * I + 1) := by
  have hweight : (Real.exp ((a - 1) * u - V * u ^ 2 / 2) : ℂ) =
      Complex.exp (-((1 - a : ℝ) : ℂ) * u) * (Real.exp (-V * u ^ 2 / 2) : ℂ) := by
    simp only [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hmain : (Complex.exp (((t : ℂ) * I + 1) * u) / ((t : ℂ) * I + 1)) *
      (Complex.exp (-((1 - a : ℝ) : ℂ) * u) * (Real.exp (-V * u ^ 2 / 2) : ℂ)) =
        Complex.exp (((a : ℂ) + (t : ℂ) * I) * u - (V : ℂ) * u ^ 2 / 2) /
          ((t : ℂ) * I + 1) := by
    rw [div_mul_eq_mul_div, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hweight, ← hmain, zetaExpRemainder]
  ring

/-- The original scale integral in Lemma 3.3 is absolutely convergent. -/
theorem integrable_source_gaussian_sum (a t V : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) :
    Integrable (fun u : ℝ => zetaSum (Real.exp u) t *
      (Real.exp ((a - 1) * u - V * u ^ 2 / 2) : ℂ)) := by
  apply ((integrable_source_gaussian_remainder a t V ha ha1 hV).add
    (integrable_source_gaussian_pole a t V hV)).congr
  filter_upwards with u
  exact (source_gaussian_sum_split a t V u).symm

/-- Exact Lemma 3.3, with its positive pole residue and source normalization.
The proof uses the convergent regularized transform and restores its main term. -/
theorem source_gaussian_identity (a t V : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hV : 0 < V) :
    (Real.sqrt (2 * Real.pi * V) : ℂ) *
      (∫ u : ℝ, zetaSum (Real.exp u) t *
        (Real.exp ((a - 1) * u - V * u ^ 2 / 2) : ℂ)) =
      (∫ ξ : ℝ, (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
        (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)) *
          (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)) +
        (2 * Real.pi : ℂ) / (1 + (t : ℂ) * I) *
          Complex.exp (((a : ℂ) + (t : ℂ) * I) ^ 2 / (2 * (V : ℂ))) := by
  have ha1 : a < 1 := by linarith
  simp_rw [source_gaussian_sum_split]
  rw [integral_add (integrable_source_gaussian_remainder a t V ha ha1 hV)
      (integrable_source_gaussian_pole a t V hV), mul_add,
    regularized_source_gaussian_identity a t V ha ha1 hV,
    integral_source_gaussian_pole a t V hV, add_comm ((t : ℂ) * I) 1]

end
end DongWangWangZhang2026

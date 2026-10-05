import DhimanKadiriQuesadaHerrera2026.AFEFirstRealCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Explicit analytic enclosures for the AFE1 numerical constants

All bounds below are real inequalities proved in Lean. No floating-point observation is used
as proof evidence.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Filter
open scoped Topology

/-- A corrected trapezoid lower bound, obtained from the first two positive logarithm terms. -/
theorem log_succ_sub_lower_second_order {x : ℝ} (hx : 0 < x) :
    1 / (2 * x) + 1 / (2 * (x + 1)) - (1 / x ^ 2 - 1 / (x + 1) ^ 2) / 12 ≤
      Real.log (x + 1) - Real.log x := by
  have hq : 0 < 2 * x + 1 := by positivity
  have hz : 1 / (2 * x + 1) < 1 := (div_lt_one hq).mpr (by linarith)
  have hl := Real.sum_range_le_log_div (by positivity : 0 ≤ 1 / (2 * x + 1)) hz 2
  norm_num [Finset.sum_range_succ] at hl
  have he : (1 + 1 / (2 * x + 1)) / (1 - 1 / (2 * x + 1)) = (x + 1) / x := by
    field_simp
    ring
  simp only [one_div] at he
  rw [he, Real.log_div (by positivity) hx.ne'] at hl
  have hrem : 0 ≤ (2 * x ^ 2 + 2 * x + 1) /
      (12 * x ^ 2 * (x + 1) ^ 2 * (2 * x + 1) ^ 3) := by positivity
  have hid : (1 / x ^ 2 - 1 / (x + 1) ^ 2) / 12 -
      (1 / (2 * x) + 1 / (2 * (x + 1)) -
        (2 / (2 * x + 1) + 2 / (3 * (2 * x + 1) ^ 3))) =
      (2 * x ^ 2 + 2 * x + 1) / (12 * x ^ 2 * (x + 1) ^ 2 * (2 * x + 1) ^ 3) := by
    field_simp
    ring
  rw [← hid] at hrem
  simp only [div_eq_mul_inv, mul_inv_rev] at hl hrem ⊢
  linarith

/-- Finite telescoping retains the second-order correction before taking the digamma limit. -/
theorem log_sub_reciprocal_sum_lower_second_order {x : ℝ} (hx : 0 < x) (N : ℕ) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) +
      1 / (2 * ((N : ℝ) + x)) + 1 / (12 * ((N : ℝ) + x) ^ 2) ≤
      Real.log ((N : ℝ) + x) - ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + x) := by
  induction N with
  | zero => simp; ring_nf; exact le_rfl
  | succ N ih =>
    have hu : 0 < (N : ℝ) + x := by positivity
    have hl := log_succ_sub_lower_second_order hu
    rw [Finset.sum_range_succ]
    push_cast
    rw [show (N : ℝ) + 1 + x = (N : ℝ) + x + 1 by ring]
    have he : (1 / ((N : ℝ) + x) ^ 2 - 1 / ((N : ℝ) + x + 1) ^ 2) / 12 =
        1 / (12 * ((N : ℝ) + x) ^ 2) - 1 / (12 * ((N : ℝ) + x + 1) ^ 2) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he] at hl
    have hh : 1 / ((N : ℝ) + x) = 2 * (1 / (2 * ((N : ℝ) + x))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hh]
    linarith

/-- A sharp explicit lower bound for the actual digamma function, valid on the whole positive axis. -/
theorem real_digamma_lower_second_order {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) ≤ (Complex.digamma (x : ℂ)).re := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_log_sub_reciprocal_sum hx)
  apply Eventually.of_forall
  intro N
  have he := log_sub_reciprocal_sum_lower_second_order hx N
  have h1 : 0 ≤ 1 / (2 * ((N : ℝ) + x)) := by positivity
  have h2 : 0 ≤ 1 / (12 * ((N : ℝ) + x) ^ 2) := by positivity
  linarith

/-- Iterating the actual digamma recurrence gives a finite rational correction. -/
theorem real_digamma_add_nat {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (Complex.digamma ((x + N : ℝ) : ℂ)).re = (Complex.digamma (x : ℂ)).re +
      ∑ n ∈ Finset.range N, 1 / (x + (n : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
      real_digamma_add_one (by positivity : 0 < x + (N : ℝ)), ih, Finset.sum_range_succ]
    ring

/-- Finite recurrence plus the second-order lower bound encloses digamma at a positive argument. -/
theorem real_digamma_lower_finite {x : ℝ} (hx : 0 < x) (N : ℕ) :
    Real.log (x + N) - 1 / (2 * (x + N)) - 1 / (12 * (x + N) ^ 2) -
      ∑ n ∈ Finset.range N, 1 / (x + (n : ℝ)) ≤ (Complex.digamma (x : ℂ)).re := by
  have he := real_digamma_lower_second_order (by positivity : 0 < x + (N : ℝ))
  rw [real_digamma_add_nat hx] at he
  linarith

/-- An explicit finite upper enclosure for Euler's constant, derived from ψ(1)=-γ. -/
theorem euler_constant_upper_finite (N : ℕ) :
    Real.eulerMascheroniConstant ≤
      (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) - Real.log ((N : ℝ) + 1) +
        1 / (2 * ((N : ℝ) + 1)) + 1 / (12 * ((N : ℝ) + 1) ^ 2) := by
  have he := real_digamma_lower_finite (by norm_num : (0 : ℝ) < 1) N
  rw [Complex.ofReal_one, real_digamma_one] at he
  simp_rw [add_comm (1 : ℝ)] at he
  linarith

/-- The rational part of the finite AFE-factor enclosure. -/
noncomputable def afeFactorRationalPart (N : ℕ) (u : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1 - u))) +
    1 / (2 * ((N : ℝ) + 1)) + 1 / (12 * ((N : ℝ) + 1) ^ 2) +
    1 / (2 * ((N : ℝ) + 1 - u)) + 1 / (12 * ((N : ℝ) + 1 - u) ^ 2) -
    1 / (2 * (1 + u)) - 1 / 2

/-- The actual AFE factor is bounded by finite reciprocals and three elementary logarithms. -/
theorem afePartIFactor_le_finite {u : ℝ} (hu : u < 1) (N : ℕ) :
    afePartIFactor u ≤ afeFactorRationalPart N u + Real.log (1 + u) -
      Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + 1 - u) := by
  have hγ := euler_constant_upper_finite N
  have hψ := real_digamma_lower_finite (by linarith : 0 < 1 - u) N
  have he (n : ℕ) : 1 - u + (n : ℝ) = (n : ℝ) + 1 - u := by ring
  simp_rw [he] at hψ
  unfold afePartIFactor afeFactorRationalPart
  rw [Finset.sum_add_distrib]
  linarith

/-- Positive logarithm partial sums, evaluated only by kernel-checked rational arithmetic later. -/
noncomputable def logRationalLower (N : ℕ) (z : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range N, z ^ (2 * n + 1) / (2 * (n : ℝ) + 1)

/-- The same partial sum with its explicit geometric remainder. -/
noncomputable def logRationalUpper (N : ℕ) (z : ℝ) : ℝ :=
  logRationalLower N z + 2 * z ^ (2 * N + 1) / (1 - z ^ 2)

/-- A finite lower enclosure for the logarithm of a rational ratio. -/
theorem logRationalLower_le {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (N : ℕ) :
    logRationalLower N z ≤ Real.log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz hz1 N
  push_cast at h
  unfold logRationalLower
  linarith

/-- A finite upper enclosure for the logarithm of a rational ratio. -/
theorem log_le_logRationalUpper {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (N : ℕ) :
    Real.log ((1 + z) / (1 - z)) ≤ logRationalUpper N z := by
  have h := Real.log_div_le_sum_range_add hz hz1 N
  push_cast at h
  unfold logRationalUpper logRationalLower
  rw [mul_div_assoc]
  linarith

/-- An entirely finite rational majorant when u is rational; the shift is exactly 32. -/
noncomputable def afeFactorRationalUpper (u : ℝ) : ℝ :=
  afeFactorRationalPart 31 u + logRationalUpper 6 (u / (2 + u)) +
    logRationalUpper 3 (u / (64 - u)) - 10 * logRationalLower 12 (1 / 3)

/-- The finite rational formula bounds the actual digamma/logarithmic AFE factor on all 0<u<1. -/
theorem afePartIFactor_le_rationalUpper {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    afePartIFactor u ≤ afeFactorRationalUpper u := by
  have ha : 0 < 2 + u := by positivity
  have hb : 0 < 64 - u := by linarith
  have hu32 : 0 < 32 - u := by linarith
  have hza : u / (2 + u) < 1 := (div_lt_one ha).mpr (by linarith)
  have hzb : u / (64 - u) < 1 := (div_lt_one hb).mpr (by linarith)
  have hA := log_le_logRationalUpper (div_pos hu ha).le hza 6
  have hB := log_le_logRationalUpper (div_pos hu hb).le hzb 3
  have hrA : (1 + u / (2 + u)) / (1 - u / (2 + u)) = 1 + u := by
    field_simp
    ring
  have hrB : (1 + u / (64 - u)) / (1 - u / (64 - u)) = 32 / (32 - u) := by
    have hd : 1 - u / (64 - u) = (2 * (32 - u)) / (64 - u) := by
      field_simp
      ring
    rw [hd]
    field_simp
    ring
  rw [hrA] at hA
  rw [hrB, Real.log_div (by norm_num) hu32.ne'] at hB
  have hL := logRationalLower_le (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1) 12
  rw [show (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 by norm_num] at hL
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hF := afePartIFactor_le_finite hu1 31
  norm_num only [Nat.cast_ofNat] at hF
  rw [h32] at hF hB
  unfold afeFactorRationalUpper
  linarith

/-- A finite rational certificate bounds m(c), with the pi and argument rounding directions explicit. -/
theorem afeFirstConstant_le_rational_certificate {c t₀ p u B : ℝ}
    (hc : 0 < c) (ht₀ : 0 < t₀) (hp : 0 < p) (hpπ : p ≤ Real.pi)
    (hcu : 1 / (2 * p * c) ≤ u) (hu1 : u < 1) (hcert : afeFactorRationalUpper u ≤ B) :
    afeFirstConstant c t₀ ≤ c + (1 / p) * (1 / t₀ + 1) * B := by
  have hu : 0 < u := (one_div_pos.mpr (by positivity : 0 < 2 * p * c)).trans_le hcu
  have ha : 0 < 1 / (2 * Real.pi * c) := by positivity
  have hau : 1 / (2 * Real.pi * c) ≤ u := by
    apply le_trans _ hcu
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hfactor := (afePartIFactor_monotone ha hau hu1).trans
    ((afePartIFactor_le_rationalUpper hu hu1).trans hcert)
  have hnonneg := afePartIFactor_nonneg ha (hau.trans_lt hu1)
  have hcoeff : (1 / Real.pi) * (1 / t₀ + 1) ≤ (1 / p) * (1 / t₀ + 1) :=
    mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hp hpπ) (by positivity)
  unfold afeFirstConstant
  exact add_le_add le_rfl (mul_le_mul hcoeff hfactor hnonneg (by positivity))

/-- A fixed rational lower bound for pi, proved from Mathlib's analytic decimal enclosure. -/
theorem afe_pi_lower : (31415926535 / 10000000000 : ℝ) ≤ Real.pi := by
  linarith [Real.pi_gt_d20]

end DhimanKadiriQuesadaHerrera2026

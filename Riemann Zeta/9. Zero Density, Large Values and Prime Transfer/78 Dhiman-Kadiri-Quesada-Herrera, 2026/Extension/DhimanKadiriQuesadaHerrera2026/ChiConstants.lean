import DhimanKadiriQuesadaHerrera2026.GammaAnchors
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The exact constants in source Lemma 6

The definitions retain the printed formulas, including the logarithmic quotient
in C₃. Its removable algebraic form is proved for positive threshold.
-/

namespace DhimanKadiriQuesadaHerrera2026

/-- The paper's C₁, with both of its nonnegative terms. -/
noncomputable def chiC1 (σ t₀ : ℝ) : ℝ :=
  (1 - σ) ^ 2 * (1 / 2 + 2 / Real.pi) +
    (1 - σ) * (σ - 1 / 2) * ((Real.pi / 2) ^ 2 + (1 - σ) / (2 * t₀))

/-- The paper's C₂. -/
noncomputable def chiC2 (t₀ : ℝ) : ℝ :=
  Real.exp (1 / (12 * t₀) + 1 / (90 * t₀ ^ 3))

/-- The literal logarithmic-quotient formula for the paper's C₃. -/
noncomputable def chiC3 (t₀ : ℝ) : ℝ :=
  (chiC2 t₀ - 1) / Real.log (chiC2 t₀) * (1 / 12 + 1 / (90 * t₀ ^ 2)) +
    t₀ * Real.exp (-Real.pi * t₀) * chiC2 t₀

/-- The literal C₀ from the source, before algebraic simplification. -/
noncomputable def chiC0 (σ t₀ : ℝ) : ℝ :=
  1 + 1 / t₀ * (chiC1 σ t₀ * (1 + Real.exp (-Real.pi * t₀)) * chiC2 t₀ + chiC3 t₀)

/-- The logarithm of C₂ is positive on every positive threshold. -/
theorem log_chiC2_pos {t₀ : ℝ} (ht : 0 < t₀) : 0 < Real.log (chiC2 t₀) := by
  rw [chiC2, Real.log_exp]
  positivity

/-- The exact printed C₀ equals its factored form, without dropping a source term. -/
theorem chiC0_eq {σ t₀ : ℝ} (ht : 0 < t₀) :
    chiC0 σ t₀ = chiC2 t₀ * (1 + Real.exp (-Real.pi * t₀)) * (1 + chiC1 σ t₀ / t₀) := by
  have hl := (log_chiC2_pos ht).ne'
  have hlog : Real.log (chiC2 t₀) = 1 / (12 * t₀) + 1 / (90 * t₀ ^ 3) := by
    rw [chiC2, Real.log_exp]
  have hscale : 1 / 12 + 1 / (90 * t₀ ^ 2) = t₀ * Real.log (chiC2 t₀) := by
    rw [hlog]
    field_simp
  unfold chiC0 chiC3
  rw [hscale]
  field_simp
  ring

/-- C₁ dominates a fixed quadratic on the full source strip. -/
theorem chiC1_quadratic_lower {σ t₀ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht : 0 < t₀) :
    (9 / 8) * (1 - σ) - (5 / 4) * (1 - σ) ^ 2 ≤ chiC1 σ t₀ := by
  have hp : 1 ≤ 1 / 2 + 2 / Real.pi := by
    have hh : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).mpr
      linarith [Real.pi_lt_four]
    linarith
  have hq : (9 / 4 : ℝ) ≤ (Real.pi / 2) ^ 2 + (1 - σ) / (2 * t₀) := by
    have hn : 0 ≤ (1 - σ) / (2 * t₀) := div_nonneg (by linarith [hσ.2]) (by positivity)
    nlinarith [Real.pi_gt_three]
  have hm1 := mul_le_mul_of_nonneg_left hp (sq_nonneg (1 - σ))
  have hm2 := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (show 0 ≤ 1 - σ by linarith [hσ.2]) (show 0 ≤ σ - 1 / 2 by linarith [hσ.1]))
  unfold chiC1
  nlinarith

/-- C₁ absorbs the distance to the nearer exact Gamma anchor. -/
theorem chiC1_anchor_distance_lower {σ t₀ : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 0 < t₀) :
    (3 / 4) * min (1 - σ) (σ - 1 / 2) ≤ chiC1 σ t₀ := by
  have h := chiC1_quadratic_lower hσ ht
  by_cases hu : 1 - σ ≤ 1 / 4
  · rw [min_eq_left (by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ 1 - σ by linarith [hσ.2]) (show 0 ≤ 1 / 4 - (1 - σ) by linarith)]
  · rw [min_eq_right (by linarith)]
    have hm := mul_nonneg (show 0 ≤ (1 - σ) - 1 / 4 by linarith)
      (show 0 ≤ 1 / 2 - (1 - σ) by linarith [hσ.1])
    nlinarith

/-- A rational chord controls the exponential on the whole half interval. -/
theorem exp_le_one_add_three_halves {a : ℝ} (ha : a ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    Real.exp a ≤ 1 + (3 / 2) * a := by
  have he : Real.exp (1 / 2 : ℝ) ≤ 7 / 4 := by
    have hs : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 / 2 : ℝ)]
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 / 2 : ℝ))
    (show 0 ≤ 1 - 2 * a by linarith [ha.2]) (show 0 ≤ 2 * a by linarith [ha.1])
    (show (1 - 2 * a) + 2 * a = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have harg : 2 * a * (1 / 2) = a := by ring
  rw [harg] at hc
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr he)]

/-- The source threshold is strictly larger than one quarter. -/
theorem chi_threshold_gt_quarter {t₀ : ℝ} (ht : 1 / Real.pi ≤ t₀) : 1 / 4 < t₀ := by
  have h : (1 / 4 : ℝ) < 1 / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_four]
  exact h.trans_le ht

/-- C₁ is nonnegative throughout the source strip. -/
theorem chiC1_nonneg {σ t₀ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 0 < t₀) :
    0 ≤ chiC1 σ t₀ := by
  have h := chiC1_anchor_distance_lower hσ ht
  have hm : 0 ≤ min (1 - σ) (σ - 1 / 2) := le_min (by linarith [hσ.2]) (by linarith [hσ.1])
  linarith

/-- The exact source C₁ absorbs the uniform exponential anchor-distance correction. -/
theorem exp_anchor_distance_le {σ t₀ t : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht₀ : 1 / Real.pi ≤ t₀) (ht : t₀ ≤ t) :
    Real.exp (min (1 - σ) (σ - 1 / 2) / (2 * t)) ≤ 1 + chiC1 σ t₀ / t₀ := by
  have hp := chi_threshold_gt_quarter ht₀
  have htpos : 0 < t₀ := by linarith
  have hm : 0 ≤ min (1 - σ) (σ - 1 / 2) := le_min (by linarith [hσ.2]) (by linarith [hσ.1])
  have hmle : min (1 - σ) (σ - 1 / 2) ≤ 1 / 4 := by
    have h₁ := min_le_left (1 - σ) (σ - 1 / 2)
    have h₂ := min_le_right (1 - σ) (σ - 1 / 2)
    linarith
  have ha : min (1 - σ) (σ - 1 / 2) / (2 * t₀) ∈ Set.Icc 0 (1 / 2 : ℝ) := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 2 * t₀)).mpr
      linarith
  calc
    _ ≤ Real.exp (min (1 - σ) (σ - 1 / 2) / (2 * t₀)) := by
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_left hm (by positivity) (by linarith)
    _ ≤ 1 + (3 / 2) * (min (1 - σ) (σ - 1 / 2) / (2 * t₀)) := exp_le_one_add_three_halves ha
    _ ≤ _ := by
      have h := div_le_div_of_nonneg_right (chiC1_anchor_distance_lower hσ htpos) htpos.le
      calc
        _ = 1 + ((3 / 4) * min (1 - σ) (σ - 1 / 2)) / t₀ := by ring
        _ ≤ _ := by linarith

/-- Squaring the preceding exponential bound gives the required Gamma correction. -/
theorem exp_anchor_distance_sq_le {σ t₀ t : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht₀ : 1 / Real.pi ≤ t₀) (ht : t₀ ≤ t) :
    Real.exp (min (1 - σ) (σ - 1 / 2) / t) ≤ (1 + chiC1 σ t₀ / t₀) ^ 2 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le (exp_anchor_distance_le hσ ht₀ ht) 2
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  rwa [show 2 * (min (1 - σ) (σ - 1 / 2) / (2 * t)) =
    min (1 - σ) (σ - 1 / 2) / t by ring] at h

/-- The exact C₂ absorbs the imaginary-anchor correction uniformly in height. -/
theorem exp_gamma_anchor_le_chiC2_sq {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    Real.exp (1 / (6 * t)) ≤ chiC2 t₀ ^ 2 := by
  unfold chiC2
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := one_div_le_one_div_of_le (show 0 < 6 * t₀ by positivity)
    (show 6 * t₀ ≤ 6 * t by linarith)
  have hn : 0 ≤ 1 / (90 * t₀ ^ 3) := by positivity
  have he : 1 / (6 * t₀) = 2 * (1 / (12 * t₀)) := by ring
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The source constant is positive, including both endpoints of the sigma interval. -/
theorem chiC0_pos {σ t₀ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 0 < t₀) :
    0 < chiC0 σ t₀ := by
  rw [chiC0_eq ht]
  have h := chiC1_nonneg hσ ht
  unfold chiC2
  positivity

end DhimanKadiriQuesadaHerrera2026

import DhimanKadiriQuesadaHerrera2026.StationaryEdges
import Mathlib.NumberTheory.Harmonic.Bounds

namespace DhimanKadiriQuesadaHerrera2026

/-- Away from zero the finite curvature cap is bounded by its reciprocal branch. -/
theorem stationaryEndpointCap_le_recip (ℓ : ℝ) {gap : ℝ} (hgap : gap ≠ 0) :
    stationaryEndpointCap ℓ gap ≤ 1 / (Real.pi * |gap|) := by
  rw [stationaryEndpointCap, if_neg hgap]
  exact min_le_right _ _

/-- The positive-index real harmonic sum has Mathlib's logarithmic bound. -/
theorem real_harmonic_sum_le (N : ℕ) :
    (∑ ν ∈ Finset.Icc 1 N, 1 / (ν : ℝ)) ≤ 1 + Real.log N := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using
    harmonic_le_one_add_log N

/-- Integral reflection reverses the exact reciprocal sum at an integer endpoint. -/
theorem reciprocal_integer_reflect (N : ℕ) :
    (∑ ν ∈ Finset.Icc 1 N, 1 / ((N : ℝ) + 1 - ν)) = ∑ ν ∈ Finset.Icc 1 N, 1 / (ν : ℝ) := by
  rw [stationary_reciprocal_backward N (by linarith : (N : ℝ) < (N : ℝ) + 1)]
  have h := stationary_reciprocal_forward N (by norm_num : (0 : ℝ) < 1)
  simpa only [sub_zero, add_sub_cancel_left] using h.symm

/-- Removing the lowest index shifts the other endpoint reciprocal sum exactly. -/
theorem reciprocal_lower_shift (M : ℕ) :
    (∑ ν ∈ Finset.Icc 2 M, 1 / ((ν : ℝ) - 1)) = ∑ ν ∈ Finset.Icc 1 (M - 1), 1 / (ν : ℝ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, sum_Icc_one_eq_sum_range_real]
  rw [show M + 1 - 2 = M - 1 by omega]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  congr 1
  ring

/-- The far-end caps left after the two mixed endpoint estimates obey the printed logarithmic bound on the full source derivative range. -/
theorem stationary_far_caps_log {α β ℓ : ℝ} {M : ℕ} (hM : 2 ≤ M)
    (hα : α < 1) (hβ : (M : ℝ) ≤ β) :
    (∑ ν ∈ Finset.Icc 1 (M - 1), stationaryEndpointCap ℓ (β - (ν : ℝ))) +
      (∑ ν ∈ Finset.Icc 2 M, stationaryEndpointCap ℓ (α - (ν : ℝ))) ≤
        2 / Real.pi * Real.log (β - α) + 1.251 := by
  have hM1 : 1 ≤ M := by omega
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM1, Nat.cast_one]
  have hleft : (∑ ν ∈ Finset.Icc 1 (M - 1), stationaryEndpointCap ℓ (β - (ν : ℝ))) ≤
      1 / Real.pi * ∑ ν ∈ Finset.Icc 1 (M - 1), 1 / (ν : ℝ) := by
    have he : (∑ ν ∈ Finset.Icc 1 (M - 1), 1 / ((M : ℝ) - (ν : ℝ))) =
        ∑ ν ∈ Finset.Icc 1 (M - 1), 1 / (ν : ℝ) := by
      have h := reciprocal_integer_reflect (M - 1)
      rw [hcast] at h
      simpa only [sub_add_cancel] using h
    rw [← he, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ν hν
    have hn : (ν : ℝ) ≤ (M : ℝ) - 1 := by exact_mod_cast (Finset.mem_Icc.mp hν).2
    have hp : 0 < β - (ν : ℝ) := by linarith
    apply (stationaryEndpointCap_le_recip ℓ hp.ne').trans
    rw [abs_of_pos hp]
    have hi := one_div_le_one_div_of_le (by linarith : 0 < (M : ℝ) - (ν : ℝ))
      (by linarith : (M : ℝ) - (ν : ℝ) ≤ β - (ν : ℝ))
    simpa only [one_div, mul_inv_rev, mul_comm] using
      mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / Real.pi)
  have hright : (∑ ν ∈ Finset.Icc 2 M, stationaryEndpointCap ℓ (α - (ν : ℝ))) ≤
      1 / Real.pi * ∑ ν ∈ Finset.Icc 1 (M - 1), 1 / (ν : ℝ) := by
    rw [← reciprocal_lower_shift M, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ν hν
    have hn : (2 : ℝ) ≤ ν := by exact_mod_cast (Finset.mem_Icc.mp hν).1
    have hp : α - (ν : ℝ) < 0 := by linarith
    apply (stationaryEndpointCap_le_recip ℓ hp.ne).trans
    rw [abs_of_neg hp, neg_sub]
    have hi := one_div_le_one_div_of_le (by linarith : 0 < (ν : ℝ) - 1)
      (by linarith : (ν : ℝ) - 1 ≤ (ν : ℝ) - α)
    simpa only [one_div, mul_inv_rev, mul_comm] using
      mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / Real.pi)
  have hlog : Real.log (M - 1 : ℕ) ≤ Real.log (β - α) := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < M - 1))
    rw [hcast]
    linarith
  have hh := (real_harmonic_sum_le (M - 1)).trans (add_le_add le_rfl hlog)
  have hs := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 / Real.pi)
  have hp : 2 / Real.pi ≤ (1.251 : ℝ) := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_d4])
  simp only [div_eq_mul_inv] at hleft hright hs hp ⊢
  nlinarith

/-- A global logarithmic lower bound controls negative logs at very short derivative ranges. -/
theorem neg_inv_sqrt_le_log {w : ℝ} (hw : 0 < w) : -(1 / Real.sqrt w) ≤ Real.log w := by
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt w))
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity : 2 * Real.sqrt w ≠ 0),
    Real.log_one, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne', Real.log_sqrt hw.le] at h
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : (1 / (2 * Real.sqrt w)) * 2 = 1 / Real.sqrt w := by ring
  linarith

/-- The zero/one-frequency small-width bound fits the exact source constant and logarithm. -/
theorem stationary_small_width_absorb {ℓ w : ℝ} (hℓ : 0 < ℓ) (hℓw : ℓ ≤ w) :
    1.856 / Real.sqrt ℓ + 2 / Real.pi ≤
      2.686 / Real.sqrt ℓ + 2 / Real.pi * Real.log w + 1.251 := by
  have hw : 0 < w := hℓ.trans_le hℓw
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hℓ) (Real.sqrt_le_sqrt hℓw)
  have hlog := neg_inv_sqrt_le_log hw
  have hp : (2 / Real.pi : ℝ) ≤ 0.83 := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_d4])
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / Real.pi)
  have hmul' := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2 / Real.pi)
  have hmul'' := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 1 / Real.sqrt ℓ)
  simp only [div_eq_mul_inv] at hmul hmul' hmul'' hp ⊢
  nlinarith

/-- Moderate derivative width absorbs both uniform endpoint errors with the printed constant. -/
theorem stationary_large_width_absorb {ℓ w : ℝ} (hw : 1 / 2 ≤ w) :
    2.5275 / Real.sqrt ℓ ≤ 2.686 / Real.sqrt ℓ + 2 / Real.pi * Real.log w + 1.251 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hw
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub] at hlog
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hp : (2 / Real.pi : ℝ) ≤ 1.251 := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_d4])
  have hmul := mul_le_mul_of_nonneg_left (show -(1 : ℝ) ≤ Real.log w by linarith)
    (by positivity : 0 ≤ 2 / Real.pi)
  have hdiv := div_le_div_of_nonneg_right (by norm_num : (2.5275 : ℝ) ≤ 2.686) (Real.sqrt_nonneg ℓ)
  linarith

/-- Separating both edge frequencies counts their two half errors as one full nonlinear error. -/
theorem norm_sum_stationary_edges {M : ℕ} (hM : 2 ≤ M) (E : ℕ → ℂ) (A B : ℕ → ℝ) (r u : ℝ)
    (hleft : ‖E 1‖ ≤ r / 2 + u + A 1) (hright : ‖E M‖ ≤ r / 2 + u + B M)
    (hmid : ∀ ν ∈ Finset.Icc 2 (M - 1), ‖E ν‖ ≤ r + A ν + B ν) :
    ‖∑ ν ∈ Finset.Icc 1 M, E ν‖ ≤ ((M - 1 : ℕ) : ℝ) * r + 2 * u +
      (∑ ν ∈ Finset.Icc 1 (M - 1), A ν) + (∑ ν ∈ Finset.Icc 2 M, B ν) := by
  have hM1 : 1 ≤ M := by omega
  have he : M = (M - 1) + 1 := by omega
  have hs : Finset.Icc 1 (M - 1) = insert 1 (Finset.Icc 2 (M - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsplit : (∑ ν ∈ Finset.Icc 1 M, E ν) = E 1 + (∑ ν ∈ Finset.Icc 2 (M - 1), E ν) + E M := by
    conv_lhs => rw [he, Finset.sum_Icc_succ_top (by omega)]
    rw [← he, hs, Finset.sum_insert (by simp)]
  have hm := (norm_sum_le _ _).trans (Finset.sum_le_sum hmid)
  have hcard : (Finset.Icc 2 (M - 1)).card = M - 2 := by rw [Nat.card_Icc]; omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard] at hm
  have hsumA : (∑ ν ∈ Finset.Icc 1 (M - 1), A ν) = A 1 + ∑ ν ∈ Finset.Icc 2 (M - 1), A ν := by
    rw [hs, Finset.sum_insert (by simp)]
  have hsumB : (∑ ν ∈ Finset.Icc 2 M, B ν) = (∑ ν ∈ Finset.Icc 2 (M - 1), B ν) + B M := by
    conv_lhs => rw [he, Finset.sum_Icc_succ_top (by omega)]
    rw [← he]
  rw [hsplit, hsumA, hsumB]
  apply (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  apply (add_le_add (add_le_add hleft hm) hright).trans_eq
  rw [Nat.cast_sub hM, Nat.cast_sub hM1]
  push_cast
  ring

end DhimanKadiriQuesadaHerrera2026

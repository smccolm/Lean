import Dubon2026.GeneralRankinSelberg
import Dubon2026.PrimitiveRamifiedBounds
import Dubon2026.PrefixEnergyBounds

/-! # Individual coefficient and ramified-prime bounds from the proved Rankin remainder -/

namespace Dubon2026

noncomputable section

/-- Taking consecutive actual square partial sums gives the corresponding individual coefficient bound. -/
theorem square_coefficient_bound_of_power_remainder {a : ℕ → ℂ} {c C β : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hb : ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C * x ^ β) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → ‖a n‖ ^ 2 ≤ B * (n : ℝ) ^ β := by
  let B := ‖a 1‖ ^ 2 + |c| + 2 * C + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hm : m = 0
  · subst m
    simp only [Nat.succ_eq_add_one, zero_add, Nat.cast_one, Real.one_rpow, mul_one]
    dsimp [B]
    linarith [abs_nonneg c]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hn1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hhi := (abs_le.mp (hb (m + 1 : ℕ) hn1)).2
  have hlo := (abs_le.mp (hb m hm1)).1
  rw [squareSummatory_nat, sum_Icc_one_eq_range_succ, Finset.sum_range_succ] at hhi
  rw [squareSummatory_nat, sum_Icc_one_eq_range_succ] at hlo
  have hp : (m : ℝ) ^ β ≤ ((m + 1 : ℕ) : ℝ) ^ β :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast (Nat.le_succ m)) hβ
  have hpow := Real.one_le_rpow hn1 hβ
  have hCpow := mul_le_mul_of_nonneg_left hp hC
  have hc : c ≤ |c| * ((m + 1 : ℕ) : ℝ) ^ β :=
    (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) hpow)
  have ht : ‖a (m + 1)‖ ^ 2 ≤ (|c| + 2 * C) * ((m + 1 : ℕ) : ℝ) ^ β := by
    push_cast at hhi hCpow hc ⊢
    nlinarith
  change ‖a (m + 1)‖ ^ 2 ≤ _
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  dsimp [B]
  nlinarith [sq_nonneg ‖a 1‖]

/-- The proved general-level Rankin error bounds every actual normalized coefficient square by a constant times n^(3/5). -/
theorem exists_normalized_cusp_coefficient_three_fifths {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 2 ≤ k) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n →
      ‖normalizedCuspCoefficients f n‖ ^ 2 ≤ B * (n : ℝ) ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_general_cusp_square_three_fifths f hk
  exact square_coefficient_bound_of_power_remainder hC.le (by norm_num) hb

/-- The exact ramified prime-power law removes the constant from the genuine Rankin pointwise bound. -/
theorem primitive_bad_coefficient_norm_sq_le_three_fifths {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q) :
    ‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 ≤ (p : ℝ) ^ (3 / 5 : ℝ) := by
  obtain ⟨B, _hB, hbound⟩ := exists_normalized_cusp_coefficient_three_fifths f.toCuspForm hk
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : ∀ r : ℕ,
      (‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 / (p : ℝ) ^ (3 / 5 : ℝ)) ^ r ≤ B := by
    intro r
    have ht := hbound (p ^ r) (Nat.one_le_pow r p hp.pos)
    rw [primitiveCuspForm_normalized_bad_prime_power f hp hpQ, norm_pow, Nat.cast_pow,
      ← Real.rpow_natCast_mul hp0.le, mul_comm (r : ℝ), Real.rpow_mul_natCast hp0.le] at ht
    rw [div_pow, div_le_iff₀ (pow_pos (Real.rpow_pos_of_pos hp0 _) r)]
    rw [← pow_mul, Nat.mul_comm 2 r, pow_mul]
    exact ht
  have hr : ‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 / (p : ℝ) ^ (3 / 5 : ℝ) ≤ 1 := by
    by_contra h
    obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt B (lt_of_not_ge h)
    exact (not_lt_of_ge (hb r)) hr
  exact (div_le_one (Real.rpow_pos_of_pos hp0 _)).mp hr

end
end Dubon2026

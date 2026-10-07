import Dubon2026.PrimeCountAsymptotics

/-! # Removing logarithmic weights from bounded genuine prime averages -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The exact finite error in removing logarithmic prime weights is controlled by the prime counting and Chebyshev sums. -/
theorem prime_log_weight_error {u : ℕ → ℝ} {C : ℝ}
    (hu : ∀ p, Nat.Prime p → |u p| ≤ C) {N : ℕ} (hN : 2 ≤ N) :
    |(∑ p ∈ Nat.primesLE N, u p) -
      (∑ p ∈ Nat.primesLE N, u p * Real.log p) / Real.log N| ≤
      C * ((Nat.primeCounting N : ℝ) - (∑ p ∈ Nat.primesLE N, Real.log p) / Real.log N) := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hweight (p : ℕ) (hp : p ∈ Nat.primesLE N) : 0 ≤ 1 - Real.log p / Real.log N := by
    obtain ⟨hpN,hp⟩ := Nat.mem_primesLE.mp hp
    have hle : Real.log (p : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpN)
    exact sub_nonneg.mpr ((div_le_one₀ hlog).mpr hle)
  have he : (∑ p ∈ Nat.primesLE N, u p) -
      (∑ p ∈ Nat.primesLE N, u p * Real.log p) / Real.log N =
      ∑ p ∈ Nat.primesLE N, u p * (1 - Real.log p / Real.log N) := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, |u p * (1 - Real.log p / Real.log N)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.primesLE N, C * (1 - Real.log p / Real.log N) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (hweight p hp)]
      exact mul_le_mul_of_nonneg_right (hu p (Nat.mem_primesLE.mp hp).2) (hweight p hp)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.primesLE_card_eq_primeCounting]

/-- The actual inclusive prime counting normalization satisfies pi(N) log(N)/N -> 1. -/
theorem tendsto_primeCounting_log_ratio :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) * Real.log N / N) atTop (𝓝 1) := by
  have he := tendsto_primeCounting_scaled (c := 1) (by norm_num)
  simpa only [one_mul, Nat.floor_natCast, div_div_eq_mul_div] using he

/-- The actual Chebyshev prime sum divided by N tends to one. -/
theorem tendsto_prime_log_sum_ratio :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, Real.log p) / (N : ℝ)) atTop (𝓝 1) := by
  have he := chebyshev_asymptotic.comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hn : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact_mod_cast (show N ≠ 0 by omega)
  have ht := (Asymptotics.isEquivalent_iff_tendsto_one hn).mp he
  change Tendsto (fun N : ℕ => Chebyshev.theta (N : ℝ) / (N : ℝ)) atTop (𝓝 1) at ht
  simpa only [Chebyshev.theta_eq_sum_primesLE_log] using ht

/-- Bounded prime coefficients have zero ordinary prime mean whenever their logarithmically weighted mean is o(N). -/
theorem prime_average_zero_of_log_weighted {u : ℕ → ℝ} {C : ℝ}
    (hu : ∀ p, Nat.Prime p → |u p| ≤ C)
    (hw : Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, u p * Real.log p) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, u p) / Nat.primeCounting N) atTop (𝓝 0) := by
  have hpos : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≠ 0 ∧ (Nat.primeCounting N : ℝ) ≠ 0 ∧ Real.log N ≠ 0 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hpn : 0 < Nat.primeCounting N := by
      rw [← Nat.primesLE_card_eq_primeCounting]
      exact Finset.card_pos.mpr ⟨2, Nat.mem_primesLE.mpr ⟨hN, Nat.prime_two⟩⟩
    exact ⟨by exact_mod_cast (show N ≠ 0 by omega), by exact_mod_cast hpn.ne',
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'⟩
  have hweighted : Tendsto (fun N : ℕ =>
      ((∑ p ∈ Nat.primesLE N, u p * Real.log p) / Real.log N) / Nat.primeCounting N)
      atTop (𝓝 0) := by
    have ht := hw.div tendsto_primeCounting_log_ratio one_ne_zero
    simp only [zero_div] at ht
    apply ht.congr'
    filter_upwards [hpos] with N hN
    simp only [Pi.div_apply]
    field_simp [hN.1, hN.2.1, hN.2.2]
  have hratio : Tendsto (fun N : ℕ =>
      ((∑ p ∈ Nat.primesLE N, Real.log p) / Real.log N) / Nat.primeCounting N)
      atTop (𝓝 1) := by
    have ht := tendsto_prime_log_sum_ratio.div tendsto_primeCounting_log_ratio one_ne_zero
    simp only [div_self one_ne_zero] at ht
    apply ht.congr'
    filter_upwards [hpos] with N hN
    simp only [Pi.div_apply]
    field_simp [hN.1, hN.2.1, hN.2.2]
  have herr : Tendsto (fun N : ℕ =>
      (∑ p ∈ Nat.primesLE N, u p) / Nat.primeCounting N -
        ((∑ p ∈ Nat.primesLE N, u p * Real.log p) / Real.log N) / Nat.primeCounting N)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => C * (1 -
      ((∑ p ∈ Nat.primesLE N, Real.log p) / Real.log N) / Nat.primeCounting N))
    · filter_upwards [eventually_ge_atTop (2 : ℕ), hpos] with N hN hpN
      rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg (Nat.primeCounting N) : (0 : ℝ) ≤ Nat.primeCounting N)]
      have he := div_le_div_of_nonneg_right (prime_log_weight_error hu hN)
        (Nat.cast_nonneg (Nat.primeCounting N) : (0 : ℝ) ≤ Nat.primeCounting N)
      convert he using 1
      field_simp [hpN.2.1]
    · simpa only [sub_self, mul_zero] using (hratio.const_sub 1).const_mul C
  have ht := herr.add hweighted
  simpa only [sub_add_cancel, zero_add] using ht

end
end Dubon2026

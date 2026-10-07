import Dubon2026.DyadicEnergyBounds

/-! # Energy and coefficient comparison for selected primes with norms in [1,2]

The bounds here apply to the actual selected subset of (N/2,N]. They are independent
of how the arithmetic selection is proved to have positive density.
-/

namespace Dubon2026

open Filter Set

theorem selected_prime_power_bounds {Q : ℕ → Finset ℕ} (hQ : IsolatedPrimeBlocks Q)
    {N : ℕ} (hN : 1 ≤ N) {σ M : ℝ} (hσ : |σ| ≤ M) {p : ℕ} (hp : p ∈ Q N) :
    Real.exp (-(2 * M * Real.log 2)) * (N : ℝ) ^ (-2 * σ) ≤ (p : ℝ) ^ (-2 * σ) ∧
      (p : ℝ) ^ (-2 * σ) ≤ Real.exp (2 * M * Real.log 2) * (N : ℝ) ^ (-2 * σ) := by
  have hp' := hQ N p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpN : (p : ℝ) ≤ N := by exact_mod_cast hp'.2.2
  have hs : |-2 * σ| ≤ 2 * M := by
    rw [abs_mul]
    norm_num
    linarith
  have hb := real_power_ratio_bounds hp0 hN0 (by linarith) (by linarith [hp'.2.1]) hs
  exact ⟨(le_div_iff₀ (Real.rpow_pos_of_pos hN0 _)).mp hb.1,
    (div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)).mp hb.2⟩

theorem selected_prime_energy_bounds {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (hQ : IsolatedPrimeBlocks Q) {N : ℕ} (hN : 1 ≤ N)
    (ha : ∀ p ∈ Q N, 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) {σ M : ℝ} (hσ : |σ| ≤ M) :
    Real.exp (-(2 * M * Real.log 2)) * ((Q N).card : ℝ) * (N : ℝ) ^ (-2 * σ) ≤
      isolatedPrimeEnergy a Q N σ ∧
    isolatedPrimeEnergy a Q N σ ≤
      4 * Real.exp (2 * M * Real.log 2) * ((Q N).card : ℝ) * (N : ℝ) ^ (-2 * σ) := by
  have hb (p : ℕ) (hp : p ∈ Q N) :
      Real.exp (-(2 * M * Real.log 2)) * (N : ℝ) ^ (-2 * σ) ≤
        ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ) ∧
      ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ) ≤
        4 * (Real.exp (2 * M * Real.log 2) * (N : ℝ) ^ (-2 * σ)) := by
    have hw := selected_prime_power_bounds hQ hN hσ hp
    have han := ha p hp
    have hr : 0 ≤ (p : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    constructor
    · have hs : 1 ≤ ‖a p‖ ^ 2 := by nlinarith [norm_nonneg (a p)]
      exact hw.1.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hr)
    · exact (mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (a p)] :
        ‖a p‖ ^ 2 ≤ 4) hr).trans (mul_le_mul_of_nonneg_left hw.2 (by norm_num))
  have hl := Finset.sum_le_sum (s := Q N) (fun p hp => (hb p hp).1)
  have hu := Finset.sum_le_sum (s := Q N) (fun p hp => (hb p hp).2)
  simp only [Finset.sum_const, nsmul_eq_mul] at hl hu
  constructor <;> unfold isolatedPrimeEnergy <;> nlinarith [hl, hu]

theorem selected_prime_energy_log_error {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (hQ : IsolatedPrimeBlocks Q) {N : ℕ} (hN : 1 ≤ N) (hcard : 0 < (Q N).card)
    (ha : ∀ p ∈ Q N, 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) {σ M : ℝ} (hσ : |σ| ≤ M) :
    |Real.log (isolatedPrimeEnergy a Q N σ) -
      (Real.log (Q N).card - 2 * σ * Real.log N)| ≤ Real.log 4 + 2 * M * Real.log 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc0 : (0 : ℝ) < (Q N).card := by exact_mod_cast hcard
  have hb := selected_prime_energy_bounds hQ hN ha hσ
  have hx : 0 < ((Q N).card : ℝ) * (N : ℝ) ^ (-2 * σ) :=
    mul_pos hc0 (Real.rpow_pos_of_pos hN0 _)
  have hlo : Real.exp (-(Real.log 4 + 2 * M * Real.log 2)) ≤
      Real.exp (-(2 * M * Real.log 2)) := by
    apply Real.exp_le_exp.mpr
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hhi : Real.exp (Real.log 4 + 2 * M * Real.log 2) =
      4 * Real.exp (2 * M * Real.log 2) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have hh := abs_log_sub_log_le_of_exp_bounds hx
    ((mul_le_mul_of_nonneg_right hlo hx.le).trans (by simpa only [mul_assoc] using hb.1))
    (by rw [hhi]; simpa only [mul_assoc] using hb.2)
  rw [Real.log_mul hc0.ne' (Real.rpow_pos_of_pos hN0 _).ne', Real.log_rpow hN0] at hh
  have he : -2 * σ * Real.log N = -(2 * σ * Real.log N) := by ring
  simpa only [he, sub_eq_add_neg, mul_assoc] using hh.2

theorem primeCoefficientComparability_of_selected_bounds {a : ℕ → ℂ}
    {Q : ℕ → Finset ℕ} (hQ : IsolatedPrimeBlocks Q)
    (ha : ∀ᶠ N in atTop, ∀ p ∈ Q N, 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) (α : ℝ) :
    PrimeCoefficientComparability a Q α := by
  intro l u _ _
  let M := max |l| |u|
  have hM : 0 ≤ M := (abs_nonneg l).trans (le_max_left _ _)
  have he : 1 ≤ Real.exp (M * Real.log 2) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hM (Real.log_nonneg (by norm_num)))
  refine ⟨2 * Real.exp (M * Real.log 2), by linarith, ?_⟩
  filter_upwards [ha] with N haN
  intro σ hσ p hp q hq
  have hp' := hQ N p hp
  have hq' := hQ N q hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq'.1.pos
  have hpN : (p : ℝ) ≤ N := by exact_mod_cast hp'.2.2
  have hqN : (q : ℝ) ≤ N := by exact_mod_cast hq'.2.2
  have hs : |-σ| ≤ M := by
    rw [abs_neg]
    apply abs_le.mpr
    have hl := (neg_abs_le l).trans hσ.1
    have hu := hσ.2.trans (le_abs_self u)
    have hMl : |l| ≤ M := le_max_left _ _
    have hMu : |u| ≤ M := le_max_right _ _
    constructor <;> linarith
  have hw := real_power_ratio_bounds hp0 hq0 (by linarith [hq'.2.1])
    (by linarith [hp'.2.1]) hs
  have hpw : 0 < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
  have hqw : 0 < (q : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hq0 _
  have hap := haN p hp
  have haq := haN q hq
  have hc : (1 / 2 : ℝ) ≤ ‖a p‖ / ‖a q‖ ∧ ‖a p‖ / ‖a q‖ ≤ 2 := by
    constructor
    · apply (le_div_iff₀ (by linarith : 0 < ‖a q‖)).mpr
      linarith
    · apply (div_le_iff₀ (by linarith : 0 < ‖a q‖)).mpr
      linarith
  rw [mul_div_mul_comm]
  constructor
  · have hh := mul_le_mul hc.1 hw.1 (Real.exp_pos _).le (by linarith : 0 ≤ ‖a p‖ / ‖a q‖)
    simpa only [Real.exp_neg, mul_inv_rev, one_div, mul_comm] using hh
  · exact mul_le_mul hc.2 hw.2 (div_pos hpw hqw).le (by norm_num)

end Dubon2026

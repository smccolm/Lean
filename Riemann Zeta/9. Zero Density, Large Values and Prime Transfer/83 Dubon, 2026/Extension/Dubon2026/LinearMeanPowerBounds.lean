import Dubon2026.LinearSummatoryPower

/-! # Sharp power-sum bounds from a genuine linear summatory estimate -/

namespace Dubon2026

open Set MeasureTheory

noncomputable section

/-- A natural linear cumulative bound gives the literal real-cutoff bound by monotonicity of the floor. -/
theorem linearSummatory_le_real {c : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, c n) ≤ B * N) {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) ≤ B * x :=
  (hb ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) hB)

/-- The true Abel integral is bounded by its explicit power integral using the linear coefficient mean. -/
theorem linearSummatory_power_integral_le {c : ℕ → ℝ} {B a b : ℝ} (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, c n) ≤ B * N) (ha : 0 < a) (p : ℝ) :
    (∫ x in Ioc a b, (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) * x ^ (-p - 1)) ≤
      B * ∫ x in Ioc a b, x ^ (-p) := by
  have hp : ContinuousOn (fun x : ℝ => x ^ (-p)) (Icc a b) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x _ (Or.inl (ha.trans_le hx.1).ne')).continuousWithinAt
  rw [← integral_const_mul]
  apply integral_mono_ae
    ((linearSummatory_integrable_power c ha (-p - 1)).mono_set Ioc_subset_Icc_self)
    ((hp.integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul B)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx0 : 0 < x := ha.trans hx.1
  calc
    _ ≤ (B * x) * x ^ (-p - 1) := mul_le_mul_of_nonneg_right
      (linearSummatory_le_real hB hb hx0.le) (Real.rpow_nonneg hx0.le _)
    _ = B * x ^ (-p) := by
      rw [mul_assoc, mul_comm x, ← Real.rpow_add_one hx0.ne']
      congr 2
      ring

/-- The exact nonlogarithmic power integral between two positive endpoints. -/
theorem integral_neg_power_Ioc {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b) (hp : p ≠ 1) :
    (∫ x in Ioc a b, x ^ (-p)) = (b ^ (1 - p) - a ^ (1 - p)) / (1 - p) := by
  rw [← intervalIntegral.integral_of_le hab,
    integral_rpow (Or.inr ⟨by intro he; apply hp; linarith, by rw [uIcc_of_le hab]; simp [not_le.mpr ha]⟩)]
  rw [show -p + 1 = 1 - p by ring]

/-- The actual initial power sum has the sharp exponent for every order strictly between zero and one. -/
theorem linearPowerSum_le {c : ℕ → ℝ} {B p : ℝ} (hc0 : c 0 = 0) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, c n) ≤ B * N)
    (hp0 : 0 < p) (hp1 : p < 1) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 0 N, c n * (n : ℝ) ^ (-p)) ≤
      B * (1 + p / (1 - p)) * (N : ℝ) ^ (1 - p) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht : (∑ n ∈ Finset.Icc 0 N, c n) * (N : ℝ) ^ (-p) ≤ B * (N : ℝ) ^ (1 - p) := by
    apply (mul_le_mul_of_nonneg_right (hb N) (Real.rpow_nonneg hN0.le (-p))).trans_eq
    rw [mul_assoc, mul_comm (N : ℝ), ← Real.rpow_add_one hN0.ne']
    congr 2
    ring
  have hi := linearSummatory_power_integral_le hB hb zero_lt_one p (b := (N : ℝ))
  rw [integral_neg_power_Ioc zero_lt_one (by exact_mod_cast hN) hp1.ne, Real.one_rpow] at hi
  rw [linearPowerSum_abel _ hc0 N p]
  apply (add_le_add ht (mul_le_mul_of_nonneg_left hi hp0.le)).trans
  have hd : 0 < 1 - p := by linarith
  have hi' : ((N : ℝ) ^ (1 - p) - 1) / (1 - p) ≤ (N : ℝ) ^ (1 - p) / (1 - p) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi' hB) hp0.le
  calc
    _ ≤ B * (N : ℝ) ^ (1 - p) + p * (B * ((N : ℝ) ^ (1 - p) / (1 - p))) := add_le_add le_rfl hh
    _ = _ := by ring

/-- The actual finite tail has a sharp decaying bound independent of its upper cutoff. -/
theorem linearPowerTail_le {c : ℕ → ℝ} {B p : ℝ} (hc : ∀ n, 0 ≤ c n) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, c n) ≤ B * N)
    (hp : 1 < p) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ioc N M, c n * (n : ℝ) ^ (-p)) ≤
      B * (1 + p / (p - 1)) * (N : ℝ) ^ (1 - p) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM0 : (0 : ℝ) < M := hN0.trans_le (Nat.cast_le.mpr hNM)
  have ht : (∑ n ∈ Finset.Icc 0 M, c n) * (M : ℝ) ^ (-p) ≤ B * (N : ℝ) ^ (1 - p) := by
    calc
      _ ≤ (B * M) * (M : ℝ) ^ (-p) := mul_le_mul_of_nonneg_right (hb M) (Real.rpow_nonneg hM0.le _)
      _ = B * (M : ℝ) ^ (1 - p) := by
        rw [mul_assoc, mul_comm (M : ℝ), ← Real.rpow_add_one hM0.ne']
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hN0 (Nat.cast_le.mpr hNM) (by linarith)) hB
  have hi := linearSummatory_power_integral_le hB hb hN0 p (b := (M : ℝ))
  rw [integral_neg_power_Ioc hN0 (Nat.cast_le.mpr hNM) hp.ne'] at hi
  have hfrac : ((M : ℝ) ^ (1 - p) - (N : ℝ) ^ (1 - p)) / (1 - p) ≤
      (N : ℝ) ^ (1 - p) / (p - 1) := by
    have he : ((M : ℝ) ^ (1 - p) - (N : ℝ) ^ (1 - p)) / (1 - p) =
        ((N : ℝ) ^ (1 - p) - (M : ℝ) ^ (1 - p)) / (p - 1) := by
      rw [show 1 - p = -(p - 1) by ring, div_neg, ← neg_div, neg_sub]
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg hM0.le (1 - p)]) (by linarith)
  have hi' := hi.trans (mul_le_mul_of_nonneg_left hfrac hB)
  have hlow : 0 ≤ (∑ n ∈ Finset.Icc 0 N, c n) * (N : ℝ) ^ (-p) := by
    exact mul_nonneg (Finset.sum_nonneg fun n _ => hc n) (Real.rpow_nonneg hN0.le _)
  rw [linearPowerTail_abel _ hN hNM p]
  have hi'' := mul_le_mul_of_nonneg_left hi' (show 0 ≤ p by linarith)
  calc
    _ ≤ B * (N : ℝ) ^ (1 - p) + p * (B * ((N : ℝ) ^ (1 - p) / (p - 1))) := by linarith
    _ = _ := by ring

end
end Dubon2026

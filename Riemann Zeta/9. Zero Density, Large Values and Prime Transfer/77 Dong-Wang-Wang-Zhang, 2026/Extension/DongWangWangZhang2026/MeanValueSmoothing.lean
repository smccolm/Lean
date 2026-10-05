import DongWangWangZhang2026.MeanValueEuler
import PrimeNumberTheoremAnd.BrunTitchmarsh

/-!
# Arithmetic smoothing for the actual cutoff sums

The installed Selberg/Brun--Titchmarsh theorem supplies a short-interval
prime majorant. Quartic cells have enough length for its error and for the
higher-prime-power contribution. This is an alternate route to the smoothing
input in GS03 Lemma 2.1, not an assumed quantitative prime number theorem.
-/

namespace DongWangWangZhang2026

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

/-- The actual prime logarithmic mass on an integer interval, with the sieve
level left free for the subsequent quartic-cell choice. -/
theorem sum_prime_log_interval_le (a b : ℕ) (z : ℝ)
    (ha : 0 < a) (hab : a < b) (hz : 1 < z) :
    (∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log p) ≤
      Real.log b * (2 * ((b : ℝ) - a) / Real.log z + 6 * z * (1 + Real.log z) ^ 3) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hBT := BrunTitchmarsh.primesBetween_le (a : ℝ) ((b : ℝ) - a) z
    haR (sub_pos.mpr habR) hz
  have hcard : (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) ≤
      BrunTitchmarsh.primesBetween a b := by
    unfold BrunTitchmarsh.primesBetween
    simp only [Nat.ceil_natCast, Nat.floor_natCast]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter Nat.Prime
      (show Finset.Ioc a b ⊆ Finset.Icc a b from fun p hp =>
        Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hp).1.le, (Finset.mem_Ioc.mp hp).2⟩))
  have hlog : 0 ≤ Real.log b := Real.log_natCast_nonneg b
  calc
    _ ≤ ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log b := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := Finset.mem_filter.mp hp
      exact Real.log_le_log (by exact_mod_cast hmem.2.pos)
        (by exact_mod_cast (Finset.mem_Ioc.mp hmem.1).2)
    _ = Real.log b * (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) := by
      simp [mul_comm]
    _ ≤ Real.log b * BrunTitchmarsh.primesBetween a b := mul_le_mul_of_nonneg_left hcard hlog
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using hBT) hlog

/-- Higher prime powers on any interval are bounded by their full non-prime
mass up to the upper endpoint; Mathlib's explicit Chebyshev estimate applies. -/
theorem sum_nonprime_mangoldt_interval_le (a b : ℕ) (hb : 1 ≤ b) :
    (∑ n ∈ (Finset.Ioc a b).filter (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n) ≤
      2 * Real.sqrt b * Real.log b := by
  apply le_trans _ (Chebyshev.psi_sub_theta_le (by exact_mod_cast hb : (1 : ℝ) ≤ b))
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hmem := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨lt_of_le_of_lt (Nat.zero_le a) (Finset.mem_Ioc.mp hmem.1).1,
        (Finset.mem_Ioc.mp hmem.1).2⟩, hmem.2⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem quarticCell_length_le {r : ℝ} (hr : 1 ≤ r) :
    (r + 1) ^ 4 - r ^ 4 ≤ 15 * r ^ 3 := by
  have h2 : r ≤ r ^ 2 := by nlinarith
  have h3 : r ^ 2 ≤ r ^ 3 := by nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr)]
  nlinarith

theorem log_one_add_quartic_le {r : ℝ} (hr : 1 ≤ r) :
    (1 + Real.log r) ^ 4 ≤ 16 * r ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hr0)
  rw [Real.log_sqrt hr0.le] at hs
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log r)
    (show 1 + Real.log r ≤ 2 * Real.sqrt r by linarith) 4
  have heq : (2 * Real.sqrt r) ^ 4 = 16 * r ^ 2 := by
    rw [mul_pow, show (Real.sqrt r) ^ 4 = ((Real.sqrt r) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hr0.le]
    norm_num
  exact h.trans_eq heq

/-- The prime mass on quartic cells has an absolute cubic bound. The sieve
level is the cell index, so its logarithmic error is absorbed explicitly. -/
theorem sum_prime_log_quarticCell_le (k : ℕ) (hk : 2 ≤ k) :
    (∑ p ∈ (Finset.Ioc (k ^ 4) ((k + 1) ^ 4)).filter Nat.Prime, Real.log p) ≤
      1008 * (k : ℝ) ^ 3 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : 0 < Real.log k := Real.log_pos (by linarith)
  have hab : k ^ 4 < (k + 1) ^ 4 := Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by decide)
  have habR : (k : ℝ) ^ 4 < ((k : ℝ) + 1) ^ 4 := by exact_mod_cast hab
  have hlen0 := sub_pos.mpr habR
  have h := sum_prime_log_interval_le (k ^ 4) ((k + 1) ^ 4) k (by positivity) hab
    (by exact_mod_cast (show 1 < k by omega))
  push_cast at h
  rw [Real.log_pow] at h
  have hlogNext : Real.log ((k : ℝ) + 1) ≤ 2 * Real.log k := by
    have hbase : (k : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < k + 1) hbase
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hmain : (4 * Real.log ((k : ℝ) + 1)) *
      (2 * (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) / Real.log k) ≤
        16 * (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) := by
    calc
      _ ≤ (8 * Real.log k) *
          (2 * (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) / Real.log k) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp; ring
  have herr : (4 * Real.log ((k : ℝ) + 1)) * (6 * k * (1 + Real.log k) ^ 3) ≤
      768 * (k : ℝ) ^ 3 := by
    calc
      _ ≤ (8 * (1 + Real.log k)) * (6 * k * (1 + Real.log k) ^ 3) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 48 * k * (1 + Real.log k) ^ 4 := by ring
      _ ≤ 48 * k * (16 * (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_left
        (log_one_add_quartic_le (by linarith)) (by positivity)
      _ = _ := by ring
  have hlen := quarticCell_length_le (r := k) (by linarith)
  rw [mul_add] at h
  linarith

/-- The actual von Mangoldt mass on every noninitial quartic cell, including
higher prime powers, has a uniform cubic majorant without a PNT premise. -/
theorem sum_mangoldt_quarticCell_le (k : ℕ) (hk : 2 ≤ k) :
    (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4), ArithmeticFunction.vonMangoldt n) ≤
      1040 * (k : ℝ) ^ 3 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hp := sum_prime_log_quarticCell_le k hk
  have hn := sum_nonprime_mangoldt_interval_le (k ^ 4) ((k + 1) ^ 4)
    (one_le_pow₀ (by omega))
  have hnonprime : (∑ n ∈ (Finset.Ioc (k ^ 4) ((k + 1) ^ 4)).filter
      (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n) ≤ 32 * (k : ℝ) ^ 3 := by
    apply hn.trans
    push_cast
    rw [Real.log_pow, show ((k : ℝ) + 1) ^ 4 = (((k : ℝ) + 1) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (k + 1) ^ 2)]
    norm_num only [Nat.cast_ofNat]
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < k + 1)
    have hsquare : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
    calc
      _ ≤ 2 * ((k : ℝ) + 1) ^ 2 * (4 * k) := mul_le_mul_of_nonneg_left
        (by linarith) (by positivity)
      _ ≤ 2 * (4 * (k : ℝ) ^ 2) * (4 * k) := by gcongr
      _ = _ := by ring
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc (k ^ 4) ((k + 1) ^ 4)) Nat.Prime ArithmeticFunction.vonMangoldt
  have hprime : (∑ n ∈ (Finset.Ioc (k ^ 4) ((k + 1) ^ 4)).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt n) =
        ∑ n ∈ (Finset.Ioc (k ^ 4) ((k + 1) ^ 4)).filter Nat.Prime, Real.log n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  rw [hprime] at hsplit
  linarith

/-- Uniform quartic-cell bound, now including the first cell. -/
theorem sum_mangoldt_quarticCell_le_uniform (k : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4), ArithmeticFunction.vonMangoldt n) ≤
      2048 * (k : ℝ) ^ 3 := by
  by_cases hk2 : 2 ≤ k
  · exact (sum_mangoldt_quarticCell_le k hk2).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  have hk1 : k = 1 := by omega
  subst k
  norm_num only [one_pow, Nat.cast_one, Nat.reduceAdd, Nat.reducePow, mul_one]
  have hsub : (∑ n ∈ Finset.Ioc 1 16, ArithmeticFunction.vonMangoldt n) ≤
      Chebyshev.psi 16 := by
    rw [Chebyshev.psi]
    norm_num only [Nat.floor_ofNat]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Ioc_subset_Ioc_left (by norm_num)
    · intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have h := Chebyshev.psi_le_const_mul_self (by norm_num : (0 : ℝ) ≤ 16)
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  linarith

theorem zetaSum_sub_eq_sum_Ioc (t : ℝ) {a b : ℝ} (hab : a ≤ b) :
    zetaSum b t - zetaSum a t = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, zetaTerm t n := by
  have hI (u : ℝ) : Finset.Icc 1 ⌊u⌋₊ = Finset.Ioc 0 ⌊u⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp only [zetaSum, hI]
  have h := Finset.sum_Ioc_consecutive (zetaTerm t) (Nat.zero_le ⌊a⌋₊)
    (Nat.floor_mono hab)
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

/-- Unit phase coefficients give a height-uniform variation bound, including
the floor jump. This controls errors when averaging over a quartic cell. -/
theorem norm_zetaSum_sub_le (t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖zetaSum b t - zetaSum a t‖ ≤ b - a + 1 := by
  rw [zetaSum_sub_eq_sum_Ioc t hab]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ‖zetaTerm t n‖ := norm_sum_le _ _
    _ = (⌊b⌋₊ - ⌊a⌋₊ : ℕ) := by
      rw [Finset.sum_congr rfl (fun n hn => norm_zetaTerm t
        (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1))]
      simp
    _ ≤ b - a + 1 := by
      rw [Nat.cast_sub (Nat.floor_mono hab)]
      have hb := Nat.floor_le (ha.trans hab)
      have ha' := Nat.lt_floor_add_one a
      linarith

theorem norm_zetaSum_le_of_mem_interval (t : ℝ) {a b u v : ℝ}
    (ha : 0 ≤ a) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
    ‖zetaSum u t‖ ≤ ‖zetaSum v t‖ + (b - a + 1) := by
  rcases le_total v u with hvu | huv
  · have h := norm_zetaSum_sub_le t (ha.trans hv.1) hvu
    have hn := norm_sub_norm_le (zetaSum u t) (zetaSum v t)
    linarith [hu.2, hv.1]
  · have h := norm_zetaSum_sub_le t (ha.trans hu.1) huv
    rw [norm_sub_rev] at h
    have hn := norm_sub_norm_le (zetaSum u t) (zetaSum v t)
    linarith [hv.2, hu.1]

theorem intervalIntegrable_zetaSum_reciprocal_norm (t x : ℝ) {a b : ℝ}
    (hx : 0 ≤ x) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ‖zetaSum (x / u) t‖) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply Measure.integrableOn_of_bounded (by simp)
    (((measurable_zetaSum t).comp (measurable_const.div measurable_id)).norm.aestronglyMeasurable)
    (M := x / a)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [norm_norm]
  exact (norm_zetaSum_le (div_nonneg hx (ha.le.trans hu.1)) t).trans
    (div_le_div_of_nonneg_left hx ha hu.1)

/-- Averaging the actual cutoff sum across a positive denominator interval
costs only its endpoint variation and the single floor jump. -/
theorem zetaSum_reciprocal_le_cell_average (t x : ℝ) {a b v : ℝ}
    (hx : 0 ≤ x) (ha : 0 < a) (hab : a < b) (hv : v ∈ Set.Icc a b) :
    (b - a) * ‖zetaSum (x / v) t‖ ≤
      (∫ u : ℝ in a..b, ‖zetaSum (x / u) t‖) +
        (b - a) * (x / a - x / b + 1) := by
  have hfi := intervalIntegrable_zetaSum_reciprocal_norm t x hx ha hab.le
  have hrec (u : ℝ) (hu : u ∈ Set.Icc a b) : x / u ∈ Set.Icc (x / b) (x / a) :=
    ⟨div_le_div_of_nonneg_left hx (ha.trans_le hu.1) hu.2,
      div_le_div_of_nonneg_left hx ha hu.1⟩
  have h := intervalIntegral.integral_mono_on hab.le (intervalIntegrable_const)
    (hfi.add intervalIntegrable_const) (fun u hu =>
      norm_zetaSum_le_of_mem_interval t (div_nonneg hx (ha.le.trans hab.le)) (hrec v hv) (hrec u hu))
  rw [intervalIntegral.integral_add hfi intervalIntegrable_const,
    intervalIntegral.integral_const, intervalIntegral.integral_const] at h
  simpa only [smul_eq_mul] using h

/-- The sieve bound genuinely controls the original summatory function on
one cell, through its integral and its proved floor-sensitive variation. -/
theorem sum_mangoldt_zetaSum_quarticCell_le (t x : ℝ) (k : ℕ)
    (hx : 0 ≤ x) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4),
      ArithmeticFunction.vonMangoldt n * ‖zetaSum (x / n) t‖) ≤
      2048 * (∫ u : ℝ in (k : ℝ) ^ 4..((k : ℝ) + 1) ^ 4, ‖zetaSum (x / u) t‖) +
        2048 * (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
          (x / (k : ℝ) ^ 4 - x / ((k : ℝ) + 1) ^ 4 + 1) := by
  let a : ℝ := (k : ℝ) ^ 4
  let b : ℝ := ((k : ℝ) + 1) ^ 4
  let J := ∫ u : ℝ in a..b, ‖zetaSum (x / u) t‖
  let E := x / a - x / b + 1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by
    dsimp [a, b]
    exact_mod_cast (Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by decide : 4 ≠ 0))
  have hlen : (k : ℝ) ^ 3 ≤ b - a := by dsimp [a, b]; nlinarith
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg_of_forall hab.le (fun _ => norm_nonneg _)
  have hE : 0 ≤ E := by
    dsimp [E]
    linarith [div_le_div_of_nonneg_left hx ha hab.le]
  have hmass := (sum_mangoldt_quarticCell_le_uniform k hk).trans
    (mul_le_mul_of_nonneg_left hlen (by norm_num : (0 : ℝ) ≤ 2048))
  have hsum := Finset.sum_le_sum (s := Finset.Ioc (k ^ 4) ((k + 1) ^ 4))
    (fun n hn => mul_le_mul_of_nonneg_left
      (zetaSum_reciprocal_le_cell_average t x hx ha hab (show (n : ℝ) ∈ Set.Icc a b from by
        have hmem := Finset.mem_Ioc.mp hn
        constructor
        · dsimp [a]; exact_mod_cast hmem.1.le
        · dsimp [b]; exact_mod_cast hmem.2)) (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
  change (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4),
      ArithmeticFunction.vonMangoldt n * ((b - a) * ‖zetaSum (x / n) t‖)) ≤
    ∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4), ArithmeticFunction.vonMangoldt n *
      (J + (b - a) * E) at hsum
  simp_rw [← mul_assoc, mul_comm (ArithmeticFunction.vonMangoldt _) (b - a), mul_assoc] at hsum
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hm := mul_le_mul_of_nonneg_right hmass (show 0 ≤ J + (b - a) * E by positivity)
  have hfinal : (b - a) * (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4),
      ArithmeticFunction.vonMangoldt n * ‖zetaSum (x / n) t‖) ≤
      (b - a) * (2048 * J + 2048 * (b - a) * E) := by
    calc
      _ ≤ _ := hsum.trans hm
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp hfinal

theorem quarticCell_variation_cost_le (x r : ℝ) (hx : 0 ≤ x) (hr : 1 ≤ r) :
    ((r + 1) ^ 4 - r ^ 4) * (x / r ^ 4 - x / (r + 1) ^ 4 + 1) ≤
      225 * x / r ^ 2 + 15 * r ^ 3 := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r + 1 := by linarith
  have hlen := quarticCell_length_le hr
  have hpow : r ^ 4 ≤ (r + 1) ^ 4 := pow_le_pow_left₀ hr0.le (by linarith) 4
  have hden : r ^ 4 * r ^ 4 ≤ r ^ 4 * (r + 1) ^ 4 :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hsq : ((r + 1) ^ 4 - r ^ 4) ^ 2 ≤ (15 * r ^ 3) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hpow) hlen 2
  have hfrac : x * ((r + 1) ^ 4 - r ^ 4) ^ 2 / (r ^ 4 * (r + 1) ^ 4) ≤
      225 * x / r ^ 2 := by
    calc
      _ ≤ x * (15 * r ^ 3) ^ 2 / (r ^ 4 * (r + 1) ^ 4) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hx) (by positivity)
      _ ≤ x * (15 * r ^ 3) ^ 2 / (r ^ 4 * r ^ 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp; ring
  have heq : ((r + 1) ^ 4 - r ^ 4) * (x / r ^ 4 - x / (r + 1) ^ 4 + 1) =
      x * ((r + 1) ^ 4 - r ^ 4) ^ 2 / (r ^ 4 * (r + 1) ^ 4) +
        ((r + 1) ^ 4 - r ^ 4) := by field_simp
  rw [heq]
  exact add_le_add hfrac hlen

theorem sum_quarticCells (f : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4), f n) =
      ∑ n ∈ Finset.Ioc 1 ((K + 1) ^ 4), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    exact Finset.sum_Ioc_consecutive f (one_le_pow₀ (by omega))
      (Nat.pow_le_pow_left (Nat.le_succ _) 4)

theorem sum_quarticCell_integrals (t x : ℝ) (K : ℕ) (hx : 0 ≤ x) :
    (∑ k ∈ Finset.Icc 1 K,
      ∫ u : ℝ in (k : ℝ) ^ 4..((k : ℝ) + 1) ^ 4, ‖zetaSum (x / u) t‖) =
      ∫ u : ℝ in 1..((K : ℝ) + 1) ^ 4, ‖zetaSum (x / u) t‖ := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact intervalIntegrable_zetaSum_reciprocal_norm t x hx (by norm_num)
        (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) K] : (1 : ℝ) ≤ K + 1))
    · exact intervalIntegrable_zetaSum_reciprocal_norm t x hx (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 4)

/-- Summing the cells yields an actual arithmetic smoothing bound. The error
has only a linear cutoff term and the fourth power of the cell endpoint. -/
theorem sum_mangoldt_zetaSum_quarticPrefix_le (t x : ℝ) (K : ℕ) (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Ioc 1 ((K + 1) ^ 4),
      ArithmeticFunction.vonMangoldt n * ‖zetaSum (x / n) t‖) ≤
      2048 * (∫ u : ℝ in 1..((K : ℝ) + 1) ^ 4, ‖zetaSum (x / u) t‖) +
        2048 * (450 * x + 15 * (K : ℝ) ^ 4) := by
  rw [← sum_quarticCells]
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 K) (fun k hk =>
    (sum_mangoldt_zetaSum_quarticCell_le t x k hx (Finset.mem_Icc.mp hk).1).trans
      (add_le_add le_rfl (show 2048 * (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
          (x / (k : ℝ) ^ 4 - x / ((k : ℝ) + 1) ^ 4 + 1) ≤
            2048 * (225 * x / (k : ℝ) ^ 2 + 15 * (k : ℝ) ^ 3) from by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (quarticCell_variation_cost_le x k hx (by exact_mod_cast (Finset.mem_Icc.mp hk).1))
          (by norm_num))))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_quarticCell_integrals t x K hx,
    ← Finset.mul_sum] at hsum
  apply hsum.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hinv : (∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have hset : Finset.Ioo 0 (K + 1) = Finset.Icc 1 K := by
      ext k
      simp only [Finset.mem_Ioo, Finset.mem_Icc]
      omega
    simpa only [hset, Nat.cast_zero, zero_add, div_one] using
      (sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1))
  have hcubes : (∑ k ∈ Finset.Icc 1 K, (k : ℝ) ^ 3) ≤ (K : ℝ) ^ 4 := by
    calc
      _ ≤ ∑ _ ∈ Finset.Icc 1 K, (K : ℝ) ^ 3 := Finset.sum_le_sum (fun k hk =>
        pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast (Finset.mem_Icc.mp hk).2) 3)
      _ = _ := by simp; ring
  simp_rw [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hinv (show 0 ≤ 225 * x by positivity)]

/-- Double integer square roots select the quartic cell containing the real
cutoff. No integrality restriction is imposed on the cutoff itself. -/
theorem exists_quarticCell_cover {x : ℝ} (hx : 1 ≤ x) :
    ∃ K : ℕ, 1 ≤ K ∧ (K : ℝ) ^ 4 ≤ x ∧ x < ((K : ℝ) + 1) ^ 4 := by
  let N := ⌊x⌋₊
  let K := Nat.sqrt (Nat.sqrt N)
  have hN : 1 ≤ N := (Nat.one_le_floor_iff _).mpr hx
  have hK : 1 ≤ K := Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr (by omega))
  have hlow : K ^ 4 ≤ N := by
    have h1 := Nat.sqrt_le' (Nat.sqrt N)
    have h2 := Nat.sqrt_le' N
    have h3 := Nat.pow_le_pow_left h1 2
    simpa only [← pow_mul] using h3.trans h2
  have hhigh : N < (K + 1) ^ 4 := by
    have h1 := Nat.lt_succ_sqrt' (Nat.sqrt N)
    have h2 := Nat.lt_succ_sqrt' N
    have h3 := Nat.pow_le_pow_left (Nat.succ_le_of_lt h1) 2
    simpa only [← pow_mul] using h2.trans_le h3
  refine ⟨K, hK, (show (K : ℝ) ^ 4 ≤ (N : ℝ) by exact_mod_cast hlow).trans
    (Nat.floor_le (zero_le_one.trans hx)), ?_⟩
  have h := (Nat.floor_lt (zero_le_one.trans hx)).mp hhigh
  exact_mod_cast h

theorem integral_zetaSum_reciprocal_eq_of_cutoff (t : ℝ) {x B : ℝ}
    (hx : 1 ≤ x) (hB : x ≤ B) :
    (∫ u : ℝ in 1..B, ‖zetaSum (x / u) t‖) =
      ∫ u : ℝ in 1..x, ‖zetaSum (x / u) t‖ := by
  have hx0 : 0 < x := by linarith
  have htail : (∫ u : ℝ in x..B, ‖zetaSum (x / u) t‖) = 0 := by
    rw [intervalIntegral.integral_of_le hB]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [zetaSum_eq_zero_of_lt_one ((div_lt_one (hx0.trans hu.1)).mpr hu.1), norm_zero]
    rfl
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_zetaSum_reciprocal_norm t x hx0.le (by norm_num) hx)
    (intervalIntegrable_zetaSum_reciprocal_norm t x hx0.le hx0 hB)
  rw [htail, add_zero] at h
  exact h.symm

/-- Arithmetic smoothing with absolute constants, proved from the sieve and
the actual sum's variation; the cutoff is an arbitrary real number. -/
theorem sum_mangoldt_zetaSum_le_integral (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * ‖zetaSum (x / n) t‖) ≤
      2048 * (∫ u : ℝ in 1..x, ‖zetaSum (x / u) t‖) + 952320 * x := by
  obtain ⟨K, _, hK, hcover⟩ := exists_quarticCell_cover hx
  have hN : ⌊x⌋₊ ≤ (K + 1) ^ 4 := by
    apply Nat.le_of_lt
    apply (Nat.floor_lt (zero_le_one.trans hx)).mpr
    exact_mod_cast hcover
  have hsub : (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n * ‖zetaSum (x / n) t‖) ≤
      ∑ n ∈ Finset.Ioc 1 ((K + 1) ^ 4),
        ArithmeticFunction.vonMangoldt n * ‖zetaSum (x / n) t‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hN)
    intro n _ _
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (norm_nonneg _)
  have h := hsub.trans (sum_mangoldt_zetaSum_quarticPrefix_le t x K (zero_le_one.trans hx))
  rw [integral_zetaSum_reciprocal_eq_of_cutoff t hx hcover.le] at h
  linarith

private theorem sum_Icc_zero_eq_sum_Icc_one (f : ℕ → ℂ) (hf : f 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, hf, zero_add]
  congr 1

/-- Exact Abel identity for the logarithmic weighting of the original sum. -/
theorem logZetaSum_eq_log_mul_sub_integral (t x : ℝ) :
    logZetaSum x t = (Real.log x : ℂ) * zetaSum x t -
      ∫ u in Set.Ioc 1 x, zetaSum u t / (u : ℂ) := by
  have hderiv (u : ℝ) (hu : u ∈ Set.Icc 1 x) :
      HasDerivAt (fun v : ℝ => (Real.log v : ℂ)) ((u⁻¹ : ℝ) : ℂ) u :=
    (Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1))).ofReal_comp
  have hcont : ContinuousOn (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) (Set.Icc 1 x) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_id.inv₀ (fun u hu =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)))
  have hint : IntegrableOn (deriv (fun v : ℝ => (Real.log v : ℂ))) (Set.Icc 1 x) :=
    hcont.integrableOn_Icc.congr_fun (fun u hu => (hderiv u hu).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₀ (zetaTerm t) (zetaTerm_zero t) x
    (fun u hu => (hderiv u hu).differentiableAt) hint
  have hsum (u : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, zetaTerm t n) = zetaSum u t :=
    sum_Icc_zero_eq_sum_Icc_one _ (zetaTerm_zero t) _
  have hlogs : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log n : ℂ) * zetaTerm t n) =
      logZetaSum x t := sum_Icc_zero_eq_sum_Icc_one _ (by simp) _
  rw [hlogs, hsum] at h
  have hi : (∫ u in Set.Ioc 1 x, deriv (fun v : ℝ => (Real.log v : ℂ)) u *
      ∑ n ∈ Finset.Icc 0 ⌊u⌋₊, zetaTerm t n) =
      ∫ u in Set.Ioc 1 x, zetaSum u t / (u : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw [(hderiv u ⟨hu.1.le, hu.2⟩).deriv, hsum, Complex.ofReal_inv]
    ring
  rwa [hi] at h

/-- Logarithmic weighting changes the actual sum by at most the cutoff;
this is uniform in the spectral height, not an asymptotic premise. -/
theorem norm_log_mul_zetaSum_sub_logZetaSum_le (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖(Real.log x : ℂ) * zetaSum x t - logZetaSum x t‖ ≤ x := by
  rw [logZetaSum_eq_log_mul_sub_integral t x, sub_sub_cancel]
  have h := norm_setIntegral_le_of_norm_le_const (f := fun u : ℝ => zetaSum u t / (u : ℂ))
    (C := 1) (by simp : volume (Set.Ioc 1 x) < ⊤) (fun u hu => by
      have hu0 : 0 < u := by linarith [hu.1]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu0.le]
      exact (div_le_one hu0).mpr (norm_zetaSum_le hu0.le t))
  simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hx), one_mul] at h
  linarith

theorem logZetaSum_eq_mangoldt_convolution (x t : ℝ) :
    logZetaSum x t = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
      (ArithmeticFunction.vonMangoldt d : ℂ) * zetaTerm t d * zetaSum (x / d) t := by
  have hI (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    ((phaseArithmetic t).pmul complexMangoldt) (phaseArithmetic t) ⌊x⌋₊
  rw [mul_comm, ← coefficientLogMul_phase] at h
  simpa only [hI, ArithmeticFunction.pmul_apply, coefficientLogMul_apply,
    phaseArithmetic_apply, complexMangoldt_apply, logZetaSum, zetaSum,
    Nat.floor_div_natCast, mul_comm (zetaTerm t _) (ArithmeticFunction.vonMangoldt _ : ℂ)] using h

theorem norm_logZetaSum_le_mangoldt_sum (x t : ℝ) :
    ‖logZetaSum x t‖ ≤
      ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * ‖zetaSum (x / n) t‖ := by
  rw [logZetaSum_eq_mangoldt_convolution]
  have hnorm : (∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
      ‖(ArithmeticFunction.vonMangoldt d : ℂ) * zetaTerm t d * zetaSum (x / d) t‖) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d * ‖zetaSum (x / d) t‖ := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [norm_mul, norm_mul, norm_zetaTerm t (Finset.mem_Icc.mp hd).1, mul_one,
      Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  apply (norm_sum_le _ _).trans_eq
  rw [hnorm]
  symm
  apply Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
    ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩)
  intro n hn hn'
  have hn1 : n = 1 := by
    have hm := Finset.mem_Icc.mp hn
    simp only [Finset.mem_Ioc, not_and] at hn'
    omega
  simp [hn1]

/-- Pointwise smoothing for the original phase sum. An absolute factor in
front of the integral suffices for the later mean-value estimates; every
arithmetic and variation input is proved above. -/
theorem norm_zetaSum_mul_log_le_reciprocal_integral (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖zetaSum x t‖ * Real.log x ≤
      2048 * (∫ u : ℝ in 1..x, ‖zetaSum (x / u) t‖) + 952321 * x := by
  have herror := norm_log_mul_zetaSum_sub_logZetaSum_le t hx
  have hnorm := norm_sub_norm_le ((Real.log x : ℂ) * zetaSum x t) (logZetaSum x t)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hx)] at hnorm
  have hsum := (norm_logZetaSum_le_mangoldt_sum x t).trans (sum_mangoldt_zetaSum_le_integral t hx)
  nlinarith

/-- Exact logarithmic change of variables in the smoothing integral. The
summatory function may jump; monotone substitution does not assume continuity. -/
theorem integral_zetaSum_reciprocal_eq_exp (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ u : ℝ in 1..x, ‖zetaSum (x / u) t‖) =
      x * ∫ v : ℝ in 0..Real.log x, Real.exp (-v) * ‖zetaSum (Real.exp v) t‖ := by
  have hx0 : 0 < x := by linarith
  have hf : ContinuousOn (fun v : ℝ => x * Real.exp (-v)) (Set.uIcc 0 (Real.log x)) :=
    (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).continuousOn
  have hd (v : ℝ) : HasDerivAt (fun v : ℝ => x * Real.exp (-v)) (-x * Real.exp (-v)) v := by
    convert ((Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)).const_mul x using 1
    ring
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun u : ℝ => ‖zetaSum (x / u) t‖) hf (fun v _ => hd v)
    (fun v _ => by have he := Real.exp_pos (-v); nlinarith)
  have htop : x * Real.exp (-Real.log x) = 1 := by rw [Real.exp_neg, Real.exp_log hx0]; field_simp
  simp only [neg_zero, Real.exp_zero, mul_one, htop, Function.comp_def] at h
  have hfun (v : ℝ) : ‖zetaSum (x / (x * Real.exp (-v))) t‖ * (-x * Real.exp (-v)) =
      -(x * (Real.exp (-v) * ‖zetaSum (Real.exp v) t‖)) := by
    rw [Real.exp_neg, div_mul_cancel_left₀ hx0.ne', inv_inv]
    ring
  simp_rw [hfun] at h
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_symm 1 x] at h
  linarith

theorem intervalIntegrable_normalized_zetaSum_exp (t a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => Real.exp (-v) * ‖zetaSum (Real.exp v) t‖) volume a b := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (by simp)
    (((Real.measurable_exp.comp measurable_neg).mul
      ((measurable_zetaSum t).comp Real.measurable_exp).norm).aestronglyMeasurable) (M := 1)
  filter_upwards with v
  change ‖Real.exp (-v) * ‖zetaSum (Real.exp v) t‖‖ ≤ 1
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  calc
    _ ≤ Real.exp (-v) * Real.exp v := mul_le_mul_of_nonneg_left
      (norm_zetaSum_le (Real.exp_pos v).le t) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The pointwise-to-logarithmic-average input for Halász is proved here by
quartic-cell sieve smoothing. Its absolute constants do not depend on height. -/
theorem norm_normalized_zetaSum_le_log_average (t : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖zetaSum x t‖ / x ≤
      2048 / Real.log x *
        (∫ v : ℝ in 0..Real.log x, Real.exp (-v) * ‖zetaSum (Real.exp v) t‖) +
          952321 / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  have h := norm_zetaSum_mul_log_le_reciprocal_integral t hx.le
  rw [integral_zetaSum_reciprocal_eq_exp t hx.le] at h
  calc
    _ ≤ (2048 * (∫ v : ℝ in 0..Real.log x,
        Real.exp (-v) * ‖zetaSum (Real.exp v) t‖) + 952321) / Real.log x :=
      (div_le_div_iff₀ hx0 hlog).mpr (by nlinarith)
    _ = _ := by ring

end
end DongWangWangZhang2026

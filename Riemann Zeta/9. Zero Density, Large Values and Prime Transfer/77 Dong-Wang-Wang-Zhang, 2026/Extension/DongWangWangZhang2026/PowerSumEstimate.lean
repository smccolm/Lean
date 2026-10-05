import DongWangWangZhang2026.ZetaSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.PSeries

/-!
# Power-sum error for the mean-comparison argument

The cellwise second-derivative remainder avoids a logarithmic loss in the length.
All integrals below are actual complex Bochner integrals.
-/

namespace DongWangWangZhang2026

open Complex MeasureTheory intervalIntegral

noncomputable section

/-- Exact complex trapezoidal remainder on a unit cell, by two integrations by parts. -/
theorem complex_unit_trapezoid_remainder (a : ℝ) (f f' f'' : ℝ → ℂ)
    (hf : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    (hi' : IntervalIntegrable f' volume a (a + 1))
    (hi'' : IntervalIntegrable f'' volume a (a + 1)) :
    (f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x) =
      ∫ x in a..a + 1, (((x - a) * (a + 1 - x) / 2 : ℝ) : ℂ) * f'' x := by
  have hab : a ≤ a + 1 := by linarith
  have hq (x : ℝ) :
      HasDerivAt (fun x : ℝ => (((x - a) * (a + 1 - x) / 2 : ℝ) : ℂ))
        ((a + 1 / 2 - x : ℝ) : ℂ) x := by
    convert ((((hasDerivAt_id x).sub_const a).mul
      ((hasDerivAt_id x).const_sub (a + 1))).div_const 2).ofReal_comp using 1
    simp only [id_eq]
    push_cast
    ring
  have hq' (x : ℝ) :
      HasDerivAt (fun x : ℝ => ((a + 1 / 2 - x : ℝ) : ℂ)) (-1) x := by
    convert ((hasDerivAt_id x).const_sub (a + 1 / 2)).ofReal_comp using 1
    simp
  have hfirst := integral_mul_deriv_eq_deriv_mul
    (fun x _ => hq x) (fun x hx => hf' x (by simpa [Set.uIcc_of_le hab] using hx))
    (show IntervalIntegrable (fun x : ℝ => ((a + 1 / 2 - x : ℝ) : ℂ))
      volume a (a + 1) from (by fun_prop : Continuous _).intervalIntegrable _ _) hi''
  have hsecond := integral_mul_deriv_eq_deriv_mul
    (fun x _ => hq' x) (fun x hx => hf x (by simpa [Set.uIcc_of_le hab] using hx))
    (intervalIntegrable_const) hi'
  simp only [sub_self, zero_mul, mul_zero, zero_div, ofReal_zero,
    add_sub_cancel_left] at hfirst
  simp only [neg_one_mul, intervalIntegral.integral_neg] at hsecond
  rw [hfirst, hsecond]
  push_cast
  ring

/-- A unit-cell error bound for a complex-valued function. -/
theorem norm_complex_unit_trapezoid_remainder_le (a M : ℝ) (f f' f'' : ℝ → ℂ)
    (hf : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    (hi' : IntervalIntegrable f' volume a (a + 1))
    (hi'' : IntervalIntegrable f'' volume a (a + 1))
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖f'' x‖ ≤ M) :
    ‖(f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x)‖ ≤ M / 8 := by
  have hab : a ≤ a + 1 := by linarith
  rw [complex_unit_trapezoid_remainder a f f' f'' hf hf' hi' hi'']
  have h := norm_integral_le_of_norm_le_const (a := a) (b := a + 1)
    (C := M / 8) (f := fun x => (((x - a) * (a + 1 - x) / 2 : ℝ) : ℂ) * f'' x) ?_
  · simpa using h
  intro x hx
  have hx' : x ∈ Set.Icc a (a + 1) := by
    exact Set.Ioc_subset_Icc_self (by simpa [Set.uIoc_of_le hab] using hx)
  have hq0 : 0 ≤ (x - a) * (a + 1 - x) / 2 := by
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hx'.1) (sub_nonneg.mpr hx'.2)) (by norm_num)
  have hq : (x - a) * (a + 1 - x) / 2 ≤ 1 / 8 := by
    nlinarith [sq_nonneg (x - a - 1 / 2)]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0]
  calc
    _ ≤ (1 / 8) * M := mul_le_mul hq (hbound x hx') (norm_nonneg _) (by norm_num)
    _ = M / 8 := by ring

/-- Real-variable differentiation of the complex power, including zero exponent. -/
theorem hasDerivAt_positive_cpow (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := by
  simpa using ((hasDerivAt_id (x : ℂ)).cpow_const (c := s) (by simp [hx])).comp_ofReal

/-- The explicit second derivative is bounded by an integrable reciprocal square. -/
theorem norm_phase_second_derivative_le (α : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖((α : ℂ) * I) * ((α : ℂ) * I - 1) * (x : ℂ) ^ ((α : ℂ) * I - 2)‖ ≤
      (α ^ 2 + |α|) / x ^ 2 := by
  have hs : ‖(α : ℂ) * I‖ = |α| := by simp
  have hs' : ‖(α : ℂ) * I - 1‖ ≤ |α| + 1 := by
    simpa [hs] using norm_sub_le ((α : ℂ) * I) 1
  rw [norm_mul, norm_mul, hs, norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (((α : ℂ) * I - 2) : ℂ).re = -2 := by simp
  rw [hre, Real.rpow_neg hx.le, Real.rpow_two]
  calc
    _ ≤ |α| * (|α| + 1) * (x ^ 2)⁻¹ := by gcongr
    _ = (α ^ 2 + |α|) / x ^ 2 := by
      rw [div_eq_mul_inv]
      congr 1
      nlinarith [sq_abs α]

/-- The source's power phase has a summable unit-cell trapezoidal error. -/
theorem norm_phase_unit_trapezoid_remainder_le (α : ℝ) {a : ℝ} (ha : 0 < a) :
    ‖((a : ℂ) ^ ((α : ℂ) * I) + ((a + 1 : ℝ) : ℂ) ^ ((α : ℂ) * I)) / 2 -
      (∫ x in a..a + 1, (x : ℂ) ^ ((α : ℂ) * I))‖ ≤
      (α ^ 2 + |α|) / a ^ 2 / 8 := by
  let s : ℂ := (α : ℂ) * I
  have hab : a ≤ a + 1 := by linarith
  have hcont (r : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ r) (Set.uIcc a (a + 1)) := by
    intro x hx
    exact (hasDerivAt_positive_cpow r
      (ha.trans_le (by simpa [Set.uIcc_of_le hab] using hx.1))).continuousAt.continuousWithinAt
  apply norm_complex_unit_trapezoid_remainder_le a ((α ^ 2 + |α|) / a ^ 2)
    (fun x : ℝ => (x : ℂ) ^ s)
    (fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    (fun x : ℝ => s * (s - 1) * (x : ℂ) ^ (s - 2))
  · intro x hx
    exact hasDerivAt_positive_cpow s (ha.trans_le hx.1)
  · intro x hx
    convert (hasDerivAt_positive_cpow (s - 1) (ha.trans_le hx.1)).const_mul s using 1
    rw [show s - 1 - 1 = s - 2 by ring]
    ring
  · exact ((hcont (s - 1)).const_mul s).intervalIntegrable
  · exact ((hcont (s - 2)).const_mul (s * (s - 1))).intervalIntegrable
  · intro x hx
    exact (norm_phase_second_derivative_le α (ha.trans_le hx.1)).trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha)
        (pow_le_pow_left₀ ha.le hx.1 2))

/-- Unit-cell errors telescope to the actual integer-cutoff sum. -/
theorem sum_unit_trapezoid_remainders (f : ℝ → ℂ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N,
      ((f n + f (n + 1)) / 2 - (∫ x in (n : ℝ)..n + 1, f x))) =
      (∑ n ∈ Finset.Icc 1 N, f n) - (f 1 + f N) / 2 - (∫ x in (1 : ℝ)..N, f x) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih, Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← integral_add_adjacent_intervals (hf 1 n) (hf n (n + 1))]
    ring

/-- Summing the reciprocal-square cell errors loses no logarithm of the cutoff. -/
theorem norm_phase_trapezoid_remainder_le (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖zetaSum N α - (1 + zetaTerm α N) / 2 -
      (∫ x in (1 : ℝ)..N, (x : ℂ) ^ ((α : ℂ) * I))‖ ≤ (α ^ 2 + |α|) / 4 := by
  have hsum : zetaSum N α = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ ((α : ℂ) * I) := by
    simp only [zetaSum, Nat.floor_natCast]
    exact Finset.sum_congr rfl (fun n hn => zetaTerm_eq_cpow α (by
      have := (Finset.mem_Icc.mp hn).1; omega))
  rw [hsum, zetaTerm_eq_cpow α (by omega)]
  have hid := sum_unit_trapezoid_remainders (fun x : ℝ => (x : ℂ) ^ ((α : ℂ) * I))
    (fun _ _ => intervalIntegrable_cpow (Or.inl (by simp))) hN
  simp only [ofReal_natCast, ofReal_one, one_cpow] at hid
  rw [← hid]
  have hseries : (∑ n ∈ Finset.Ico 1 N, ((n : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have hset : Finset.Ioo 0 N = Finset.Ico 1 N := by
      ext n
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      omega
    simpa only [hset, Nat.cast_zero, zero_add, div_one] using
      (sum_Ioo_inv_sq_le (α := ℝ) 0 N)
  calc
    _ ≤ ∑ n ∈ Finset.Ico 1 N,
        ‖((n : ℂ) ^ ((α : ℂ) * I) + ((n + 1 : ℝ) : ℂ) ^ ((α : ℂ) * I)) / 2 -
          (∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ ((α : ℂ) * I))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico 1 N, (α ^ 2 + |α|) / (n : ℝ) ^ 2 / 8 := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_phase_unit_trapezoid_remainder_le α (by
        exact_mod_cast (Finset.mem_Ico.mp hn).1)
    _ = ((α ^ 2 + |α|) / 8) * ∑ n ∈ Finset.Ico 1 N, ((n : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ ((α ^ 2 + |α|) / 8) * 2 :=
      mul_le_mul_of_nonneg_left hseries (by positivity)
    _ = (α ^ 2 + |α|) / 4 := by ring

/-- The integer-cutoff power sum differs from its integral main term by a uniform error. -/
theorem norm_zetaSum_nat_sub_powerMain_le (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖zetaSum N α - (N : ℂ) ^ ((α : ℂ) * I + 1) / ((α : ℂ) * I + 1)‖ ≤
      2 + (α ^ 2 + |α|) / 4 := by
  let s : ℂ := (α : ℂ) * I
  have hid : (∫ x in (1 : ℝ)..N, (x : ℂ) ^ s) =
      ((N : ℂ) ^ (s + 1) - 1) / (s + 1) := by
    simpa using (integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := s)
      (Or.inl (by dsimp [s]; norm_num)))
  have hden : 1 ≤ ‖s + 1‖ := by simpa [s] using Complex.re_le_norm (s + 1)
  have hinv : ‖(1 : ℂ) / (s + 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (zero_lt_one.trans_le hden)).mpr hden
  have hboundary : ‖(1 + zetaTerm α N) / 2‖ ≤ 1 := by
    have h := norm_add_le (1 : ℂ) (zetaTerm α N)
    rw [norm_one, norm_zetaTerm α (by omega)] at h
    rw [norm_div]
    norm_num only [norm_ofNat]
    exact (div_le_one (by norm_num)).mpr (by linarith)
  have heq : zetaSum N α - (N : ℂ) ^ (s + 1) / (s + 1) =
      (zetaSum N α - (1 + zetaTerm α N) / 2 -
        (∫ x in (1 : ℝ)..N, (x : ℂ) ^ s)) +
      ((1 + zetaTerm α N) / 2 - 1 / (s + 1)) := by
    rw [hid]
    ring
  rw [show (α : ℂ) * I = s from rfl, heq]
  calc
    _ ≤ ‖zetaSum N α - (1 + zetaTerm α N) / 2 -
        (∫ x in (1 : ℝ)..N, (x : ℂ) ^ s)‖ +
      ‖(1 + zetaTerm α N) / 2 - 1 / (s + 1)‖ := norm_add_le _ _
    _ ≤ (α ^ 2 + |α|) / 4 + (1 + 1) :=
      add_le_add (norm_phase_trapezoid_remainder_le α hN)
        ((norm_sub_le _ _).trans (add_le_add hboundary hinv))
    _ = 2 + (α ^ 2 + |α|) / 4 := by ring

/-- Uniform in every real cutoff at least one; the terminal fractional interval is included. -/
theorem norm_zetaSum_sub_powerMain_le (α : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖zetaSum x α - (x : ℂ) ^ ((α : ℂ) * I + 1) / ((α : ℂ) * I + 1)‖ ≤
      4 * (1 + α ^ 2) := by
  let N := ⌊x⌋₊
  let s : ℂ := (α : ℂ) * I
  have hN : 1 ≤ N := Nat.floor_pos.mpr hx
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hid : (x : ℂ) ^ (s + 1) / (s + 1) -
      (N : ℂ) ^ (s + 1) / (s + 1) =
      ∫ u in (N : ℝ)..x, (u : ℂ) ^ s := by
    rw [integral_cpow (Or.inl (by dsimp [s]; norm_num)), ← sub_div, ofReal_natCast]
  have htail : ‖∫ u in (N : ℝ)..x, (u : ℂ) ^ s‖ ≤ 1 := by
    have hb := norm_integral_le_of_norm_le_const (a := (N : ℝ)) (b := x)
      (C := 1) (f := fun u : ℝ => (u : ℂ) ^ s) (fun u hu => ?_)
    · exact hb.trans (by simpa [N] using Nat.abs_sub_floor_le (zero_le_one.trans hx))
    have hu' : u ∈ Set.Ioc (N : ℝ) x := by simpa [Set.uIoc_of_le hNx] using hu
    rw [norm_cpow_eq_rpow_re_of_pos (hNp.trans hu'.1)]
    simp [s]
  have hsum : zetaSum x α = zetaSum N α := by simp [zetaSum, N]
  have heq : zetaSum x α - (x : ℂ) ^ (s + 1) / (s + 1) =
      (zetaSum N α - (N : ℂ) ^ (s + 1) / (s + 1)) -
        (∫ u in (N : ℝ)..x, (u : ℂ) ^ s) := by
    rw [← hid, hsum]
    ring
  rw [show (α : ℂ) * I = s from rfl, heq]
  calc
    _ ≤ ‖zetaSum N α - (N : ℂ) ^ (s + 1) / (s + 1)‖ +
      ‖∫ u in (N : ℝ)..x, (u : ℂ) ^ s‖ := norm_sub_le _ _
    _ ≤ 2 + (α ^ 2 + |α|) / 4 + 1 :=
      add_le_add (norm_zetaSum_nat_sub_powerMain_le α hN) htail
    _ ≤ 4 * (1 + α ^ 2) := by nlinarith [sq_nonneg (|α| - 1), sq_abs α, sq_nonneg α]

theorem norm_powerMain_le (α : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ((α : ℂ) * I + 1) / ((α : ℂ) * I + 1)‖ ≤ x := by
  have hden : 1 ≤ ‖(α : ℂ) * I + 1‖ := by
    simpa using Complex.re_le_norm ((α : ℂ) * I + 1)
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (((α : ℂ) * I + 1) : ℂ).re = 1 := by simp
  rw [hre, Real.rpow_one]
  simpa using div_le_div_of_nonneg_left hx.le zero_lt_one hden

/-- Both uniform bounds needed to split the Möbius coefficient sum at `x/(1+α²)`. -/
theorem norm_zetaSum_sub_powerMain_le_min (α : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖zetaSum x α - (x : ℂ) ^ ((α : ℂ) * I + 1) / ((α : ℂ) * I + 1)‖ ≤
      min (4 * (1 + α ^ 2)) (2 * x) := by
  refine le_min (norm_zetaSum_sub_powerMain_le α hx) ?_
  have h := (norm_sub_le (zetaSum x α) _).trans
    (add_le_add (norm_zetaSum_le (zero_le_one.trans hx) α)
      (norm_powerMain_le α (zero_lt_one.trans_le hx)))
  simpa only [two_mul] using h

end
end DongWangWangZhang2026

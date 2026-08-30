import PrimeShell.PrimeTerm

namespace PrimeShell

noncomputable section

open scoped BigOperators
open Zeta23 Zeta23.PrimeSide

/-- The exact ordered dyadic difference-frequency pair contribution. -/
def dyadicDifferencePair (Φ : ℝ → ℝ) (T : ℝ) (n m : ℕ) : ℝ :=
  acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m)

/-- The literal two-orientation kernel for the positive shift `h`. -/
def dyadicShiftKernel (Φ : ℝ → ℝ) (T : ℝ) (n h : ℕ) : ℝ :=
  Aminus Φ T (Real.log n) (Real.log (n + h)) +
    Aminus Φ T (Real.log (n + h)) (Real.log n)

/-- Actual weighted von Mangoldt correlation summand produced by the source coefficients. -/
def dyadicLambdaWeight (n h : ℕ) : ℝ := acoef n * acoef (n + h)

/-- The actual dyadic weighted von Mangoldt correlation at shift `h`, with the
source coefficient normalization `Λ(n)Λ(n+h)/sqrt(n(n+h))` and the exact
right-endpoint truncation. -/
def dyadicLambdaCorrelation (N h : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    if n + h ∈ Finset.Ioc N (2 * N) then dyadicLambdaWeight n h else 0

/-- A scalar-in-`h` anchor for the literal two-variable trace kernel.  The
choice `N+1` is the first integer in the dyadic block when `N>0`. -/
def anchoredDyadicShiftKernel (Φ : ℝ → ℝ) (T : ℝ) (N h : ℕ) : ℝ :=
  dyadicShiftKernel Φ T (N + 1) h

/-- The exact price of replacing the literal `(n,h)` kernel by its dyadic
anchor.  No regularity estimate is hidden in this definition. -/
def dyadicKernelVariationRemainder
    (Φ : ℝ → ℝ) (T : ℝ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc N (2 * N),
    if n + h ∈ Finset.Ioc N (2 * N) then
      dyadicLambdaWeight n h *
        (dyadicShiftKernel Φ T n h - anchoredDyadicShiftKernel Φ T N h)
    else 0

/-- Exact shifted dyadic sum, including its endpoint condition. -/
def dyadicShiftSum (Φ : ℝ → ℝ) (T : ℝ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc N (2 * N),
    if n + h ∈ Finset.Ioc N (2 * N) then
      dyadicLambdaWeight n h * dyadicShiftKernel Φ T n h else 0

/-- Exact scalar-kernel/correlation decomposition, including the complete
two-variable kernel-variation remainder. -/
theorem dyadicShiftSum_eq_kernel_mul_correlation_add_remainder
    (Φ : ℝ → ℝ) (T : ℝ) (N H : ℕ) :
    dyadicShiftSum Φ T N H =
      (∑ h ∈ Finset.Icc 1 H,
        anchoredDyadicShiftKernel Φ T N h * dyadicLambdaCorrelation N h) +
      dyadicKernelVariationRemainder Φ T N H := by
  unfold dyadicShiftSum dyadicLambdaCorrelation dyadicKernelVariationRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N)
  · simp only [hmem, if_true]
    ring
  · simp [hmem]

/-- Exact absolute-error ledger for the kernel-variation remainder.  The
right side retains the literal source kernel, endpoint indicator, arithmetic
normalization, and both dyadic positions; no unspecified bounded weight is
introduced. -/
theorem abs_dyadicKernelVariationRemainder_le_literal_sum
    (Φ : ℝ → ℝ) (T : ℝ) (N H : ℕ) :
    |dyadicKernelVariationRemainder Φ T N H| ≤
      ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc N (2 * N),
        if n + h ∈ Finset.Ioc N (2 * N) then
          dyadicLambdaWeight n h *
            (|dyadicShiftKernel Φ T n h| +
              |anchoredDyadicShiftKernel Φ T N h|)
        else 0 := by
  unfold dyadicKernelVariationRemainder
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro h hh
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro n hn
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N)
  · simp only [hmem, if_true, abs_mul]
    have hw : 0 ≤ dyadicLambdaWeight n h :=
      mul_nonneg (acoef_nonneg n) (acoef_nonneg (n + h))
    rw [abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) hw
  · simp [hmem]

/-- The arithmetic correlation vanishes outside the exact dyadic shift
support.  In fact the endpoint convention already forces `h < N`. -/
theorem dyadicLambdaCorrelation_eq_zero_of_N_le_h
    {N h : ℕ} (hNh : N ≤ h) :
    dyadicLambdaCorrelation N h = 0 := by
  unfold dyadicLambdaCorrelation
  apply Finset.sum_eq_zero
  intro n hn
  have hnlow : N < n := (Finset.mem_Ioc.mp hn).1
  have hhigh : 2 * N < n + h := by omega
  have hnot : n + h ∉ Finset.Ioc N (2 * N) := by
    rw [Finset.mem_Ioc]
    omega
  simp [hnot]

/-- The literal kernel contribution has no tail beyond `h=N`, independently
of any analytic estimate. -/
theorem dyadicShiftSum_eq_of_N_le_H
    (Φ : ℝ → ℝ) (T : ℝ) (N H : ℕ) (hNH : N ≤ H) :
    dyadicShiftSum Φ T N H = dyadicShiftSum Φ T N N := by
  unfold dyadicShiftSum
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hNH)]
  intro h hhH hhN
  have hNlt : N < h := by
    have hhH' := Finset.mem_Icc.mp hhH
    by_contra hnot
    exact hhN (Finset.mem_Icc.mpr ⟨hhH'.1, Nat.le_of_not_gt hnot⟩)
  apply Finset.sum_eq_zero
  intro n hn
  have hnlow : N < n := (Finset.mem_Ioc.mp hn).1
  have hhigh : 2 * N < n + h := by omega
  have hnot : n + h ∉ Finset.Ioc N (2 * N) := by
    rw [Finset.mem_Ioc]
    omega
  simp [hnot]

/-- Source coefficients are nonnegative, so every arithmetic correlation
weight in the exact shift rewrite is nonnegative. -/
theorem dyadicLambdaWeight_nonneg (n h : ℕ) :
    0 ≤ dyadicLambdaWeight n h := by
  exact mul_nonneg (acoef_nonneg n) (acoef_nonneg (n + h))

/-- Difference-frequency analogue of Zeta23's `abs_Aplus_le`. -/
theorem abs_Aminus_le
    (hΦ : Continuous Φ) (hΦ2 : MeasureTheory.Integrable fun x => Φ x ^ 2)
    {T y y' : ℝ} (hne : y - y' ≠ 0) :
    |Aminus Φ T y y'| ≤ 2 / |y - y'| * ∫ x, Φ x ^ 2 := by
  unfold Aminus
  have hint : MeasureTheory.IntegrableOn
      (fun x => Φ x ^ 2 * JmK T y y' x) (Set.Icc (-T) T) :=
    ((hΦ.pow 2).mul (continuous_JmK T y y')).integrableOn_Icc
  calc
    |∫ x in Set.Icc (-T) T, Φ x ^ 2 * JmK T y y' x| ≤
        ∫ x in Set.Icc (-T) T, |Φ x ^ 2 * JmK T y y' x| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x in Set.Icc (-T) T, Φ x ^ 2 * (2 / |y - y'|) := by
      apply MeasureTheory.setIntegral_mono_on hint.abs
        (hΦ2.integrableOn.mul_const _) measurableSet_Icc
      intro x hx
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact abs_Jker_le hne (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
    _ = 2 / |y - y'| * ∫ x in Set.Icc (-T) T, Φ x ^ 2 := by
      rw [MeasureTheory.integral_mul_const]
      ring
    _ ≤ 2 / |y - y'| * ∫ x, Φ x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact MeasureTheory.setIntegral_le_integral hΦ2
        (Filter.Eventually.of_forall fun x => sq_nonneg _)

/-- Explicit nonresonant size bound for the literal two-orientation kernel. -/
theorem abs_dyadicShiftKernel_le
    (hΦ : Continuous Φ) (hΦ2 : MeasureTheory.Integrable fun x => Φ x ^ 2)
    {T : ℝ} {n h : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) :
    |dyadicShiftKernel Φ T n h| ≤
      4 / |Real.log n - Real.log (n + h)| * ∫ x, Φ x ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsumpos : (0 : ℝ) < n + h := by positivity
  have hcast : (n : ℝ) < n + h := by exact_mod_cast Nat.lt_add_of_pos_right hh
  have hlog : Real.log n < Real.log (n + h) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hnpos) (Set.mem_Ioi.mpr hsumpos) hcast
  have hne : Real.log n - Real.log (n + h) ≠ 0 := sub_ne_zero.mpr hlog.ne
  have hne' : Real.log (n + h) - Real.log n ≠ 0 := sub_ne_zero.mpr hlog.ne'
  unfold dyadicShiftKernel
  calc
    |Aminus Φ T (Real.log n) (Real.log (n + h)) +
        Aminus Φ T (Real.log (n + h)) (Real.log n)| ≤
        |Aminus Φ T (Real.log n) (Real.log (n + h))| +
          |Aminus Φ T (Real.log (n + h)) (Real.log n)| := abs_add_le _ _
    _ ≤ (2 / |Real.log n - Real.log (n + h)| * ∫ x, Φ x ^ 2) +
        (2 / |Real.log (n + h) - Real.log n| * ∫ x, Φ x ^ 2) :=
      add_le_add (abs_Aminus_le hΦ hΦ2 hne) (abs_Aminus_le hΦ hΦ2 hne')
    _ = 4 / |Real.log n - Real.log (n + h)| * ∫ x, Φ x ^ 2 := by
      rw [abs_sub_comm (Real.log (n + h)) (Real.log n)]
      ring

theorem offDiagonal_eq_strictUpperTriangle
    (S : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ S, ∑ m ∈ S, if n = m then 0 else f n m) =
      ∑ n ∈ S, ∑ m ∈ S, if n < m then f n m + f m n else 0 := by
  have hpoint : ∀ n m : ℕ, (if n = m then 0 else f n m) =
      (if n < m then f n m else 0) + (if m < n then f n m else 0) := by
    intro n m
    rcases lt_trichotomy n m with h | h | h
    · simp [h, h.ne, Nat.not_lt_of_ge h.le]
    · simp [h]
    · simp [h, h.ne', Nat.not_lt_of_ge h.le]
  simp_rw [hpoint, Finset.sum_add_distrib]
  have hswap : (∑ n ∈ S, ∑ m ∈ S, if m < n then f n m else 0) =
      ∑ n ∈ S, ∑ m ∈ S, if n < m then f m n else 0 := by
    rw [Finset.sum_comm]
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hnm : n < m
  · simp [hnm]
  · simp [hnm]

private theorem strictUpperTriangle_eq_shiftSum
    (Φ : ℝ → ℝ) (T : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N), ∑ m ∈ Finset.Ioc N (2 * N),
      if n < m then dyadicDifferencePair Φ T n m + dyadicDifferencePair Φ T m n else 0) =
      dyadicShiftSum Φ T N N := by
  let S := Finset.Ioc N (2 * N)
  have hfixed : ∀ n ∈ S,
      (∑ m ∈ S with n < m,
        (dyadicDifferencePair Φ T n m + dyadicDifferencePair Φ T m n)) =
      ∑ h ∈ Finset.Icc 1 N with n + h ∈ S,
        dyadicLambdaWeight n h * dyadicShiftKernel Φ T n h := by
    intro n hn
    apply Finset.sum_bij'
        (fun m _ => m - n) (fun h _ => n + h)
    · intro m hm
      simp only [Finset.mem_filter] at hm ⊢
      rcases hm with ⟨hmS, hnm⟩
      have hnlow : N < n := (Finset.mem_Ioc.mp hn).1
      have hmhigh : m ≤ 2 * N := (Finset.mem_Ioc.mp hmS).2
      constructor
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · rw [Nat.add_sub_of_le hnm.le]
        exact hmS
    · intro h hh
      simp only [Finset.mem_filter] at hh ⊢
      rcases hh with ⟨hhIcc, hmem⟩
      exact ⟨hmem, Nat.lt_add_of_pos_right (Finset.mem_Icc.mp hhIcc).1⟩
    · intro m hm
      simp only [Finset.mem_filter] at hm
      rcases hm with ⟨hmS, hnm⟩
      exact Nat.add_sub_of_le hnm.le
    · intro h hh
      simp only [Finset.mem_filter] at hh
      exact Nat.add_sub_cancel_left n h
    · intro m hm
      simp only [Finset.mem_filter] at hm
      rcases hm with ⟨hmS, hnm⟩
      unfold dyadicDifferencePair dyadicLambdaWeight dyadicShiftKernel
      have hadd : n + (m - n) = m := Nat.add_sub_of_le hnm.le
      rw [← Nat.cast_add, hadd]
      ring
  unfold dyadicShiftSum
  change (∑ n ∈ S, ∑ m ∈ S, if n < m then
      dyadicDifferencePair Φ T n m + dyadicDifferencePair Φ T m n else 0) = _
  simp_rw [← Finset.sum_filter]
  calc
    (∑ n ∈ S, ∑ m ∈ S with n < m,
        (dyadicDifferencePair Φ T n m + dyadicDifferencePair Φ T m n)) =
        ∑ n ∈ S, ∑ h ∈ Finset.Icc 1 N with n + h ∈ S,
          dyadicLambdaWeight n h * dyadicShiftKernel Φ T n h := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hfixed n hn
    _ = ∑ h ∈ Finset.Icc 1 N, ∑ n ∈ S with n + h ∈ S,
          dyadicLambdaWeight n h * dyadicShiftKernel Φ T n h := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]

/-- Exact `m = n + h` rewrite of the complete dyadic difference-frequency off-diagonal. -/
theorem dyadicDifferenceOffDiagonal_eq_shiftSum (Φ : ℝ → ℝ) (T : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N), ∑ m ∈ Finset.Ioc N (2 * N),
      if n = m then 0 else dyadicDifferencePair Φ T n m) =
      dyadicShiftSum Φ T N N := by
  rw [offDiagonal_eq_strictUpperTriangle]
  exact strictUpperTriangle_eq_shiftSum Φ T N

end

end PrimeShell

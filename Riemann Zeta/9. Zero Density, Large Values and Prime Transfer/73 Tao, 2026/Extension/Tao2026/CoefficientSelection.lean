import Tao2026.CoefficientBounds

/-!
# Polynomial coefficient selection for Tao's Lemma 3.2

The interval is split into two nonempty disjoint halves.  The logarithmic
coefficient-product estimate bounds the sum on either half, and finite
averaging selects one polynomially bounded coefficient from each.  Combining
these positions with the canonical powerful-core decomposition proves the
full nonzero-shift relation of Lemma 3.2 with an explicit absolute exponent.
-/

namespace Tao2026

open scoped BigOperators

noncomputable def leftCoefficientHalf (N H : ℕ) : Finset ℕ :=
  Finset.Ioc N (N + H / 2)

noncomputable def rightCoefficientHalf (N H : ℕ) : Finset ℕ :=
  Finset.Ioc (N + H / 2) (N + H)

theorem card_leftCoefficientHalf (N H : ℕ) :
    (leftCoefficientHalf N H).card = H / 2 := by
  simp [leftCoefficientHalf]

theorem card_rightCoefficientHalf (N H : ℕ) :
    (rightCoefficientHalf N H).card = H - H / 2 := by
  simp [rightCoefficientHalf]
  omega

private theorem leftCoefficientHalf_subset (N H : ℕ) :
    leftCoefficientHalf N H ⊆ consecutiveInterval N H := by
  intro k hk
  simp only [leftCoefficientHalf, consecutiveInterval, Finset.mem_Ioc] at hk ⊢
  omega

private theorem rightCoefficientHalf_subset (N H : ℕ) :
    rightCoefficientHalf N H ⊆ consecutiveInterval N H := by
  intro k hk
  simp only [rightCoefficientHalf, consecutiveInterval, Finset.mem_Ioc] at hk ⊢
  omega

theorem log_intervalCoefficientProduct (N H : ℕ) :
    Real.log (intervalCoefficientProduct N H : ℝ) =
      ∑ k ∈ consecutiveInterval N H, Real.log (singleExponentPart k) := by
  rw [intervalCoefficientProduct, Nat.cast_prod]
  rw [Real.log_prod]
  intro k hk
  norm_cast
  exact (singleExponentPart_pos (by
    have := (Finset.mem_Ioc.mp hk).1
    omega)).ne'

private theorem log_singleExponentPart_nonneg
    {N H k : ℕ} (hk : k ∈ consecutiveInterval N H) :
    0 ≤ Real.log (singleExponentPart k) := by
  apply Real.log_nonneg
  exact_mod_cast singleExponentPart_pos (by
    have := (Finset.mem_Ioc.mp hk).1
    omega)

theorem log_intervalCoefficientProduct_le_polynomial
    {N H : ℕ} (hveryBad : IsVeryBadInterval N H) (hH : 2 ≤ H) :
    Real.log (intervalCoefficientProduct N H : ℝ) ≤
      coefficientExponentConstant * H * Real.log H := by
  calc
    Real.log (intervalCoefficientProduct N H : ℝ) ≤
        Real.log (smallPrimeCoefficientEnvelope H : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast intervalCoefficientProduct_pos N H
      · exact_mod_cast Nat.le_of_dvd (smallPrimeCoefficientEnvelope_pos H)
          (intervalCoefficientProduct_dvd_smallPrimeEnvelope hveryBad)
    _ ≤ coefficientExponentConstant * H * Real.log H :=
      log_smallPrimeCoefficientEnvelope_le_polynomial H hH

private theorem half_log_sum_le_polynomial
    {N H : ℕ} (hveryBad : IsVeryBadInterval N H) (hH : 2 ≤ H)
    {s : Finset ℕ} (hs : s ⊆ consecutiveInterval N H) :
    ∑ k ∈ s, Real.log (singleExponentPart k) ≤
      coefficientExponentConstant * H * Real.log H := by
  calc
    ∑ k ∈ s, Real.log (singleExponentPart k) ≤
        ∑ k ∈ consecutiveInterval N H,
          Real.log (singleExponentPart k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intro k hk _
      exact log_singleExponentPart_nonneg hk
    _ = Real.log (intervalCoefficientProduct N H : ℝ) :=
      (log_intervalCoefficientProduct N H).symm
    _ ≤ coefficientExponentConstant * H * Real.log H :=
      log_intervalCoefficientProduct_le_polynomial hveryBad hH

private theorem three_mul_half_card_ge
    (N H : ℕ) (hH : 2 ≤ H) :
    H ≤ 3 * (leftCoefficientHalf N H).card ∧
      H ≤ 3 * (rightCoefficientHalf N H).card := by
  rw [card_leftCoefficientHalf, card_rightCoefficientHalf]
  omega

private theorem half_constant_sum_ge_polynomial
    (H : ℕ) (hH : 2 ≤ H)
    {s : Finset ℕ} (hcard : H ≤ 3 * s.card) :
    coefficientExponentConstant * H * Real.log H ≤
      ∑ _k ∈ s, 3 * coefficientExponentConstant * Real.log H := by
  have hscale : 0 ≤ coefficientExponentConstant * Real.log H := by
    exact mul_nonneg coefficientExponentConstant_pos.le
      (Real.log_nonneg (by exact_mod_cast hH.trans' (by omega : 1 ≤ 2)))
  have hcardReal : (H : ℝ) ≤ 3 * s.card := by exact_mod_cast hcard
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    coefficientExponentConstant * H * Real.log H =
        (H : ℝ) * (coefficientExponentConstant * Real.log H) := by ring_nf
    _ ≤ (3 * s.card : ℝ) *
        (coefficientExponentConstant * Real.log H) := by gcongr
    _ = (s.card : ℝ) *
        (3 * coefficientExponentConstant * Real.log H) := by ring_nf

private theorem exists_in_half_with_small_log
    {N H : ℕ} (hveryBad : IsVeryBadInterval N H) (hH : 2 ≤ H)
    {s : Finset ℕ} (hs : s ⊆ consecutiveInterval N H)
    (hsNonempty : s.Nonempty) (hcard : H ≤ 3 * s.card) :
    ∃ k ∈ s, Real.log (singleExponentPart k) ≤
      3 * coefficientExponentConstant * Real.log H := by
  apply Finset.exists_le_of_sum_le hsNonempty
  exact (half_log_sum_le_polynomial hveryBad hH hs).trans
    (half_constant_sum_ge_polynomial H hH hcard)

private theorem log_bound_iff_polynomial_bound
    {H a : ℕ} (hH : 2 ≤ H) (ha : 0 < a) :
    Real.log a ≤ 3 * coefficientExponentConstant * Real.log H ↔
      (a : ℝ) ≤ (H : ℝ) ^ (3 * coefficientExponentConstant) := by
  rw [Real.log_le_iff_le_exp (by exact_mod_cast ha)]
  rw [Real.rpow_def_of_pos (by positivity)]
  ring_nf

theorem exists_two_polynomially_bounded_coefficients
    {N H : ℕ} (hveryBad : IsVeryBadInterval N H) (hH : 2 ≤ H) :
    ∃ k₁ k₂ : ℕ,
      k₁ ∈ consecutiveInterval N H ∧
      k₂ ∈ consecutiveInterval N H ∧ k₁ < k₂ ∧
      (singleExponentPart k₁ : ℝ) ≤
        (H : ℝ) ^ (3 * coefficientExponentConstant) ∧
      (singleExponentPart k₂ : ℝ) ≤
        (H : ℝ) ^ (3 * coefficientExponentConstant) := by
  have hcards := three_mul_half_card_ge N H hH
  have hleftNonempty : (leftCoefficientHalf N H).Nonempty := by
    rw [← Finset.card_pos, card_leftCoefficientHalf]
    omega
  have hrightNonempty : (rightCoefficientHalf N H).Nonempty := by
    rw [← Finset.card_pos, card_rightCoefficientHalf]
    omega
  obtain ⟨k₁, hk₁, hk₁Log⟩ := exists_in_half_with_small_log
    hveryBad hH (leftCoefficientHalf_subset N H) hleftNonempty hcards.1
  obtain ⟨k₂, hk₂, hk₂Log⟩ := exists_in_half_with_small_log
    hveryBad hH (rightCoefficientHalf_subset N H) hrightNonempty hcards.2
  have hk₁Interval := leftCoefficientHalf_subset N H hk₁
  have hk₂Interval := rightCoefficientHalf_subset N H hk₂
  refine ⟨k₁, k₂, hk₁Interval, hk₂Interval, ?_, ?_, ?_⟩
  · have hk₁' := Finset.mem_Ioc.mp hk₁
    have hk₂' := Finset.mem_Ioc.mp hk₂
    omega
  · exact (log_bound_iff_polynomial_bound hH
      (singleExponentPart_pos (by
        have := (Finset.mem_Ioc.mp hk₁Interval).1
        omega))).mp hk₁Log
  · exact (log_bound_iff_polynomial_bound hH
      (singleExponentPart_pos (by
        have := (Finset.mem_Ioc.mp hk₂Interval).1
        omega))).mp hk₂Log

/-- Tao's Lemma 3.2, with a single explicit absolute exponent.  A very bad
interval of length at least two supplies two distinct interval elements whose
canonical squarefree coefficients are polynomially bounded.  Their powerful
cores therefore satisfy the required nonzero-shift relation. -/
theorem veryBadInterval_exists_polynomial_powerfulRelation
    {N H : ℕ} (hveryBad : IsVeryBadInterval N H) (hH : 2 ≤ H) :
    ∃ a b n m h : ℕ,
      0 < h ∧ h < H ∧
      Powerful n ∧ Powerful m ∧
      a * n + h = b * m ∧
      a ∣ H.factorial ∧ b ∣ H.factorial ∧
      (a : ℝ) ≤ (H : ℝ) ^ (3 * coefficientExponentConstant) ∧
      (b : ℝ) ≤ (H : ℝ) ^ (3 * coefficientExponentConstant) ∧
      a * n ∈ consecutiveInterval N H ∧
      b * m ∈ consecutiveInterval N H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk₁k₂, hk₁Bound, hk₂Bound⟩ :=
    exists_two_polynomially_bounded_coefficients hveryBad hH
  have hk₁Eq := singleExponentPart_mul_powerfulCore
    (n := k₁) (by
      have := (Finset.mem_Ioc.mp hk₁).1
      omega)
  have hk₂Eq := singleExponentPart_mul_powerfulCore
    (n := k₂) (by
      have := (Finset.mem_Ioc.mp hk₂).1
      omega)
  refine ⟨singleExponentPart k₁, singleExponentPart k₂,
    powerfulCore k₁, powerfulCore k₂, k₂ - k₁,
    Nat.sub_pos_of_lt hk₁k₂, ?_,
    powerful_powerfulCore (by
      have := (Finset.mem_Ioc.mp hk₁).1
      omega),
    powerful_powerfulCore (by
      have := (Finset.mem_Ioc.mp hk₂).1
      omega), ?_,
    singleExponentPart_dvd_factorial_length_of_veryBad hveryBad hk₁,
    singleExponentPart_dvd_factorial_length_of_veryBad hveryBad hk₂,
    hk₁Bound, hk₂Bound, ?_, ?_⟩
  · have hk₁Mem := Finset.mem_Ioc.mp hk₁
    have hk₂Mem := Finset.mem_Ioc.mp hk₂
    omega
  · omega
  · simpa only [hk₁Eq] using hk₁
  · simpa only [hk₂Eq] using hk₂

end Tao2026

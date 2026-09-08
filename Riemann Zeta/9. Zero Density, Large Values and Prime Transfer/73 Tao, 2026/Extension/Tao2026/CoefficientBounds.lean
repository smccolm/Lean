import Tao2026.CoefficientProduct
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Quantitative bounds for the Lemma 3.2 coefficient envelope

Finite Abel summation and Chebyshev's explicit upper bound for `theta` give
an explicit `O(log H)` estimate for `sum_{p ≤ H} log p / p`.  Applied to
the exact small-prime envelope from `CoefficientProduct`, this yields a fixed
positive `C` for which the logarithm of the envelope is at most
`C * H * log H` for `H ≥ 2`.
-/

namespace Tao2026

open scoped BigOperators Chebyshev

noncomputable def primeLog (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

noncomputable def weightedPrimeLogSum (H : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 H).filter Nat.Prime, Real.log p / p

theorem sum_range_primeLog (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), primeLog k = Chebyshev.theta n := by
  calc
    ∑ k ∈ Finset.range (n + 1), primeLog k =
        ∑ k ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log k := by
      simp [primeLog, Finset.sum_filter]
    _ = ∑ k ∈ (Finset.Icc 0 n).filter Nat.Prime, Real.log k := by
      congr 2
      ext k
      simp
    _ = Chebyshev.theta n := by
      rw [Chebyshev.theta_eq_sum_Icc]
      simp

theorem weightedPrimeLogSum_eq_sum_Ioc (H : ℕ) :
    weightedPrimeLogSum H =
      ∑ n ∈ Finset.Ioc 0 H, (n : ℝ)⁻¹ * primeLog n := by
  have hsets :
      (Finset.Icc 2 H).filter Nat.Prime =
        (Finset.Ioc 0 H).filter Nat.Prime := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · intro h
      exact ⟨⟨by omega, h.1.2⟩, h.2⟩
    · exact fun h ↦ ⟨⟨h.2.two_le, h.1.2⟩, h.2⟩
  rw [weightedPrimeLogSum, hsets]
  simp [primeLog, Finset.sum_filter, div_eq_mul_inv, mul_comm]

theorem weightedPrimeLogSum_abel (H : ℕ) (hH : 0 < H) :
    weightedPrimeLogSum H =
      (H : ℝ)⁻¹ * Chebyshev.theta H +
        ∑ i ∈ Finset.Ioc 0 (H - 1),
          Chebyshev.theta i / ((i : ℝ) * (i + 1)) := by
  rw [weightedPrimeLogSum_eq_sum_Ioc]
  have hab := Finset.sum_Ioc_by_parts
    (f := fun n : ℕ ↦ (n : ℝ)⁻¹) (g := primeLog) hH
  simp only [smul_eq_mul, sum_range_primeLog] at hab
  rw [hab]
  simp only [Nat.cast_zero, Nat.cast_one, zero_add, inv_one,
    Chebyshev.theta_zero, mul_zero, sub_zero]
  have hsum :
      ∑ i ∈ Finset.Ioc 0 (H - 1),
          (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * Chebyshev.theta i =
        -∑ i ∈ Finset.Ioc 0 (H - 1),
          Chebyshev.theta i / ((i : ℝ) * (i + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hiPos : (0 : ℝ) < i := by
      exact_mod_cast (Finset.mem_Ioc.mp hi).1
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hiPos]
    ring
  rw [hsum]
  ring

private theorem inverseSuccessorSum_le_harmonic (H : ℕ) :
    ∑ i ∈ Finset.Ioc 0 (H - 1), ((i : ℝ) + 1)⁻¹ ≤
      (harmonic H : ℝ) := by
  calc
    ∑ i ∈ Finset.Ioc 0 (H - 1), ((i : ℝ) + 1)⁻¹ ≤
        ∑ i ∈ Finset.Ioc 0 (H - 1), (i : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      apply inv_anti₀
      · exact_mod_cast (Finset.mem_Ioc.mp hi).1
      · norm_num
    _ ≤ ∑ i ∈ Finset.Icc 1 H, (i : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_Ioc, Finset.mem_Icc] at hi ⊢
        omega
      · intro i _ _
        positivity
    _ = (harmonic H : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem weightedPrimeLogSum_le (H : ℕ) (hH : 0 < H) :
    weightedPrimeLogSum H ≤
      Real.log 4 * (2 + Real.log H) := by
  rw [weightedPrimeLogSum_abel H hH]
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hendpoint :
      (H : ℝ)⁻¹ * Chebyshev.theta H ≤ Real.log 4 := by
    calc
      (H : ℝ)⁻¹ * Chebyshev.theta H ≤
          (H : ℝ)⁻¹ * (Real.log 4 * H) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = Real.log 4 := by
        field_simp
  have hsummand (i : ℕ) (hi : i ∈ Finset.Ioc 0 (H - 1)) :
      Chebyshev.theta i / ((i : ℝ) * (i + 1)) ≤
        Real.log 4 * ((i : ℝ) + 1)⁻¹ := by
    have hiPos : (0 : ℝ) < i := by
      exact_mod_cast (Finset.mem_Ioc.mp hi).1
    calc
      Chebyshev.theta i / ((i : ℝ) * (i + 1)) ≤
          (Real.log 4 * i) / ((i : ℝ) * (i + 1)) := by
        apply div_le_div_of_nonneg_right
        · exact Chebyshev.theta_le_log4_mul_x (by positivity)
        · positivity
      _ = Real.log 4 * ((i : ℝ) + 1)⁻¹ := by
        field_simp [ne_of_gt hiPos]
  have hsum :
      ∑ i ∈ Finset.Ioc 0 (H - 1),
          Chebyshev.theta i / ((i : ℝ) * (i + 1)) ≤
        Real.log 4 * (harmonic H : ℝ) := by
    calc
      ∑ i ∈ Finset.Ioc 0 (H - 1),
          Chebyshev.theta i / ((i : ℝ) * (i + 1)) ≤
          ∑ i ∈ Finset.Ioc 0 (H - 1),
            Real.log 4 * ((i : ℝ) + 1)⁻¹ := by
        exact Finset.sum_le_sum hsummand
      _ = Real.log 4 *
          ∑ i ∈ Finset.Ioc 0 (H - 1), ((i : ℝ) + 1)⁻¹ := by
        rw [Finset.mul_sum]
      _ ≤ Real.log 4 * (harmonic H : ℝ) := by
        gcongr
        exact inverseSuccessorSum_le_harmonic H
  calc
    (H : ℝ)⁻¹ * Chebyshev.theta H +
        ∑ i ∈ Finset.Ioc 0 (H - 1),
          Chebyshev.theta i / ((i : ℝ) * (i + 1)) ≤
        Real.log 4 + Real.log 4 * (harmonic H : ℝ) := add_le_add hendpoint hsum
    _ ≤ Real.log 4 + Real.log 4 * (1 + Real.log H) := by
      gcongr
      exact harmonic_le_one_add_log H
    _ = Real.log 4 * (2 + Real.log H) := by ring

theorem log_smallPrimeCoefficientEnvelope (H : ℕ) :
    Real.log (smallPrimeCoefficientEnvelope H : ℝ) =
      ∑ p ∈ (Finset.Icc 2 H).filter Nat.Prime,
        (H / p + 1 : ℕ) * Real.log p := by
  rw [smallPrimeCoefficientEnvelope, Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    norm_cast
    exact pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero

theorem log_smallPrimeCoefficientEnvelope_le (H : ℕ) :
    Real.log (smallPrimeCoefficientEnvelope H : ℝ) ≤
      (H : ℝ) * weightedPrimeLogSum H + Chebyshev.theta H := by
  rw [log_smallPrimeCoefficientEnvelope]
  have hterm (p : ℕ) (hp : p ∈ (Finset.Icc 2 H).filter Nat.Prime) :
      ((H / p + 1 : ℕ) : ℝ) * Real.log p ≤
        ((H : ℝ) / p + 1) * Real.log p := by
    apply mul_le_mul_of_nonneg_right
    · simp only [Nat.cast_add, Nat.cast_one]
      linarith [show ((H / p : ℕ) : ℝ) ≤ (H : ℝ) / p from
        Nat.cast_div_le]
    · exact Real.log_nonneg (by
        exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  calc
    ∑ p ∈ (Finset.Icc 2 H).filter Nat.Prime,
        ((H / p + 1 : ℕ) : ℝ) * Real.log p ≤
      ∑ p ∈ (Finset.Icc 2 H).filter Nat.Prime,
        ((H : ℝ) / p + 1) * Real.log p := Finset.sum_le_sum hterm
    _ = (H : ℝ) * weightedPrimeLogSum H + Chebyshev.theta H := by
      rw [weightedPrimeLogSum, Chebyshev.theta_eq_sum_Icc]
      simp only [Nat.floor_natCast]
      have hsets :
          (Finset.Icc 0 H).filter Nat.Prime =
            (Finset.Icc 2 H).filter Nat.Prime := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro hp
          exact ⟨⟨hp.2.two_le, hp.1.2⟩, hp.2⟩
        · intro hp
          exact ⟨⟨Nat.zero_le _, hp.1.2⟩, hp.2⟩
      rw [hsets]
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        ring
      · simp

theorem log_smallPrimeCoefficientEnvelope_le_explicit
    (H : ℕ) (hH : 0 < H) :
    Real.log (smallPrimeCoefficientEnvelope H : ℝ) ≤
      Real.log 4 * H * (3 + Real.log H) := by
  calc
    Real.log (smallPrimeCoefficientEnvelope H : ℝ) ≤
        (H : ℝ) * weightedPrimeLogSum H + Chebyshev.theta H :=
      log_smallPrimeCoefficientEnvelope_le H
    _ ≤ (H : ℝ) * (Real.log 4 * (2 + Real.log H)) +
        Real.log 4 * H := by
      gcongr
      · exact weightedPrimeLogSum_le H hH
      · exact Chebyshev.theta_le_log4_mul_x (by positivity)
    _ = Real.log 4 * H * (3 + Real.log H) := by ring

noncomputable def coefficientExponentConstant : ℝ :=
  Real.log 4 * (1 + 3 / Real.log 2)

theorem coefficientExponentConstant_pos : 0 < coefficientExponentConstant := by
  rw [coefficientExponentConstant]
  positivity

theorem log_smallPrimeCoefficientEnvelope_le_polynomial
    (H : ℕ) (hH : 2 ≤ H) :
    Real.log (smallPrimeCoefficientEnvelope H : ℝ) ≤
      coefficientExponentConstant * H * Real.log H := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogH : Real.log 2 ≤ Real.log H := by
    gcongr
    exact_mod_cast hH
  have haux :
      3 + Real.log H ≤ (1 + 3 / Real.log 2) * Real.log H := by
    have hratio : 3 ≤ 3 / Real.log 2 * Real.log H := by
      calc
        3 = 3 / Real.log 2 * Real.log 2 := by field_simp
        _ ≤ 3 / Real.log 2 * Real.log H := by gcongr
    linarith
  calc
    Real.log (smallPrimeCoefficientEnvelope H : ℝ) ≤
        Real.log 4 * H * (3 + Real.log H) :=
      log_smallPrimeCoefficientEnvelope_le_explicit H (by omega)
    _ ≤ Real.log 4 * H * ((1 + 3 / Real.log 2) * Real.log H) := by
      gcongr
    _ = coefficientExponentConstant * H * Real.log H := by
      rw [coefficientExponentConstant]
      ring

end Tao2026

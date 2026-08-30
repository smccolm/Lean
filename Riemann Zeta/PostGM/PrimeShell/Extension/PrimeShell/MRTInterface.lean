import PrimeShell.Admissible
import PrimeShell.LocalizedCorrelation
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace PrimeShell

noncomputable section

open scoped BigOperators ArithmeticFunction

/-- The local Hardy--Littlewood factor for the ordered prime-pair shift
`h`.  This fixes the source convention `ν_p(h)=1` when `p ∣ h` and `2`
otherwise. -/
def primePairLocalFactor (h : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - (1 : ℝ) / (p : ℕ))⁻¹ ^ 2 *
    (1 - (if (p : ℕ) ∣ h then (1 : ℝ) else 2) / (p : ℕ))

/-- The literal Hardy--Littlewood singular series used in MRT Theorem
1.3(i).  Convergence and its averaged forms are separate proof
obligations; the arithmetic interface does not replace it by an opaque
function. -/
def primePairSingularSeries (h : ℕ) : ℝ :=
  ∏' p : Nat.Primes, primePairLocalFactor h p

/-- The positive-shift von-Mangoldt correlation in the exact dyadic
`(X,2X]` convention of MRT Theorem 1.3(i). -/
def mrtLambdaCorrelation (X h : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (2 * X),
    ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt (n + h)

/-- Shifts at which the MRT asymptotic fails with the displayed constant
and logarithmic saving. -/
def mrtBadPositiveShifts (C A : ℝ) (X H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).filter fun h =>
    C * X / Real.log X ^ A <
      |mrtLambdaCorrelation X h - primePairSingularSeries h * X|

/-- A faithful positive-shift specialization of MRT Theorem 1.3(i).

It records arbitrary logarithmic power, the strict epsilon margins, the
range `X^(8/33+eps) ≤ H ≤ X^(1-eps)`, the exceptional-set cardinality,
and the pointwise asymptotic outside that set.  This is a proposition
describing the external arithmetic theorem, not a proof or project axiom. -/
def MRTLambdaAlmostAllPositive : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε → ε < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X H : ℕ,
      X₀ ≤ X → 2 ≤ X →
      (X : ℝ) ^ (8 / 33 + ε) ≤ H →
      (H : ℝ) ≤ (X : ℝ) ^ (1 - ε) →
      ((mrtBadPositiveShifts C A X H).card : ℝ) ≤
          C * H / Real.log X ^ A ∧
      ∀ h ∈ Finset.Icc 1 H,
        h ∉ mrtBadPositiveShifts C A X H →
        |mrtLambdaCorrelation X h - primePairSingularSeries h * X| ≤
          C * X / Real.log X ^ A

/-- The literal weighted discrepancy left after subtracting the MRT
singular-series main term. -/
def mrtWeightedDiscrepancy
    (K : ℕ → ℝ) (X H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H,
    K h * (mrtLambdaCorrelation X h - primePairSingularSeries h * X)

/-- Finite good/bad-shift consumer.  It keeps the exact singular series,
kernel, good error, bad error, and exceptional-set size visible. -/
theorem abs_mrtWeightedDiscrepancy_le_of_good_bad
    {K : ℕ → ℝ} {X H : ℕ} {bad : Finset ℕ}
    {Kmax E B R : ℝ}
    (hKmax : 0 ≤ Kmax) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hK : ∀ h ∈ Finset.Icc 1 H, |K h| ≤ Kmax)
    (hgood : ∀ h ∈ Finset.Icc 1 H, h ∉ bad →
      |mrtLambdaCorrelation X h - primePairSingularSeries h * X| ≤ E)
    (hbad : ∀ h ∈ Finset.Icc 1 H, h ∈ bad →
      |mrtLambdaCorrelation X h - primePairSingularSeries h * X| ≤ B)
    (hcard : ((bad ∩ Finset.Icc 1 H).card : ℝ) ≤ R) :
    |mrtWeightedDiscrepancy K X H| ≤
      (H : ℝ) * Kmax * E + R * Kmax * B := by
  unfold mrtWeightedDiscrepancy
  calc
    |∑ h ∈ Finset.Icc 1 H,
        K h * (mrtLambdaCorrelation X h - primePairSingularSeries h * X)| ≤
        ∑ h ∈ Finset.Icc 1 H,
          |K h * (mrtLambdaCorrelation X h - primePairSingularSeries h * X)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 H,
        if h ∈ bad then Kmax * B else Kmax * E := by
      apply Finset.sum_le_sum
      intro h hh
      rw [abs_mul]
      split_ifs with hb
      · exact mul_le_mul (hK h hh) (hbad h hh hb)
          (abs_nonneg _) hKmax
      · exact mul_le_mul (hK h hh) (hgood h hh hb)
          (abs_nonneg _) hKmax
    _ = ((bad ∩ Finset.Icc 1 H).card : ℝ) * (Kmax * B) +
        (((Finset.Icc 1 H) \ bad).card : ℝ) * (Kmax * E) := by
      have hnot : (Finset.Icc 1 H).filter (fun h => h ∉ bad) =
          Finset.Icc 1 H \ bad := by
        ext h
        simp
      rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.Icc 1 H) (fun h => h ∈ bad)]
      rw [hnot]
      simp only [Finset.filter_mem_eq_inter, Finset.inter_comm]
      congr 1
      · calc
          (∑ x ∈ bad ∩ Finset.Icc 1 H,
              if x ∈ bad then Kmax * B else Kmax * E) =
              ∑ _x ∈ bad ∩ Finset.Icc 1 H, Kmax * B := by
                apply Finset.sum_congr rfl
                intro x hx
                simp [(Finset.mem_inter.mp hx).1]
          _ = ((bad ∩ Finset.Icc 1 H).card : ℝ) * (Kmax * B) := by simp
      · calc
          (∑ x ∈ Finset.Icc 1 H \ bad,
              if x ∈ bad then Kmax * B else Kmax * E) =
              ∑ _x ∈ Finset.Icc 1 H \ bad, Kmax * E := by
                apply Finset.sum_congr rfl
                intro x hx
                simp [(Finset.mem_sdiff.mp hx).2]
          _ = (((Finset.Icc 1 H \ bad).card : ℝ) * (Kmax * E)) := by simp
    _ ≤ R * (Kmax * B) + (H : ℝ) * (Kmax * E) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hKmax hB)
      · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hKmax hE)
        exact_mod_cast (show ((Finset.Icc 1 H \ bad).card : ℕ) ≤ H by
          calc
            (Finset.Icc 1 H \ bad).card ≤ (Finset.Icc 1 H).card :=
              Finset.card_le_card Finset.sdiff_subset
            _ ≤ H := by simp)
    _ = (H : ℝ) * Kmax * E + R * Kmax * B := by ring

/-- Direct finite consumer of `MRTLambdaAlmostAllPositive`.  The only
additional input is a uniform estimate on the genuinely exceptional
shifts; it is displayed as `B` and is not hidden in the MRT hypothesis. -/
theorem mrtLambdaAlmostAllPositive_weighted
    (hMRT : MRTLambdaAlmostAllPositive)
    {K : ℕ → ℝ} {A ε : ℝ}
    (hA : 0 < A) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X H : ℕ,
      X₀ ≤ X → 2 ≤ X →
      (X : ℝ) ^ (8 / 33 + ε) ≤ H →
      (H : ℝ) ≤ (X : ℝ) ^ (1 - ε) →
      ∀ Kmax B : ℝ,
        0 ≤ Kmax → 0 ≤ B →
        (∀ h ∈ Finset.Icc 1 H, |K h| ≤ Kmax) →
        (∀ h ∈ Finset.Icc 1 H,
          h ∈ mrtBadPositiveShifts C A X H →
          |mrtLambdaCorrelation X h - primePairSingularSeries h * X| ≤ B) →
        |mrtWeightedDiscrepancy K X H| ≤
          (H : ℝ) * Kmax * (C * X / Real.log X ^ A) +
            (C * H / Real.log X ^ A) * Kmax * B := by
  obtain ⟨C, hC, X₀, hMRT'⟩ := hMRT A ε hA hε hε'
  refine ⟨C, hC, X₀, ?_⟩
  intro X H hX hXtwo hHlower hHupper Kmax B hKmax hB hK hbad
  obtain ⟨hcard, hgood⟩ := hMRT' X H hX hXtwo hHlower hHupper
  apply abs_mrtWeightedDiscrepancy_le_of_good_bad
      hKmax (by positivity) hB hK hgood hbad
  calc
    (((mrtBadPositiveShifts C A X H) ∩ Finset.Icc 1 H).card : ℝ) ≤
        ((mrtBadPositiveShifts C A X H).card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    _ ≤ C * H / Real.log X ^ A := hcard

end

end PrimeShell

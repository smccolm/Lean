import Tao2026.BadIntervalRandomModel

/-!
# Elementary anti-sieve bounds for Proposition 6.6

This module begins the three-way anti-sieve split.  It disposes of the
deterministic branch in which the sieving prime divides the interval shift:
the total logarithmic weight of such primes is bounded by the logarithm of
the shift itself, independently of the sampled tuple.
-/

namespace Tao2026

noncomputable section

/-- The full logarithmic divisibility weight from primes dividing a fixed
positive shift.  Restricting the prime range can only decrease this quantity. -/
def taoExceptionalShiftPrimeWeight
    (m' l : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ p ∈ l.primeFactors,
    taoPrimeDivisibilityIndicator m' l p ω * Real.log p

/-- The squarefree kernel of a positive natural has logarithm at most the
logarithm of the natural. -/
theorem sum_log_primeFactors_le_log {l : ℕ} (hl : 0 < l) :
    (∑ p ∈ l.primeFactors, Real.log p) ≤ Real.log l := by
  have hnonzero : ∀ p ∈ l.primeFactors, (p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hprodDvd : ∏ p ∈ l.primeFactors, p ∣ l :=
    Nat.prod_primeFactors_dvd l
  have hprodPos : 0 < ∏ p ∈ l.primeFactors, p := by
    exact Nat.pos_of_dvd_of_pos hprodDvd hl
  have hprodLe : ∏ p ∈ l.primeFactors, p ≤ l :=
    Nat.le_of_dvd hl hprodDvd
  calc
    (∑ p ∈ l.primeFactors, Real.log p) =
        Real.log (∏ p ∈ l.primeFactors, (p : ℝ)) := by
      symm
      exact Real.log_prod hnonzero
    _ = Real.log ((∏ p ∈ l.primeFactors, p : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ Real.log l := by
      exact Real.log_le_log (by exact_mod_cast hprodPos)
        (by exact_mod_cast hprodLe)

/-- Pointwise disposal of the exceptional `p ∣ l` branch. -/
theorem taoExceptionalShiftPrimeWeight_le_log
    (m' : ℕ) {l : ℕ} (hl : 0 < l) (ω : TaoPrimeTuple) :
    taoExceptionalShiftPrimeWeight m' l ω ≤ Real.log l := by
  calc
    taoExceptionalShiftPrimeWeight m' l ω ≤
        ∑ p ∈ l.primeFactors, Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hlog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
      simpa using mul_le_mul_of_nonneg_right
        (taoPrimeDivisibilityIndicator_le_one m' l p ω) hlog
    _ ≤ Real.log l := sum_log_primeFactors_le_log hl

/-- Exceptional-prime contribution summed over the source shifts
`1 ≤ l < H`. -/
def taoExceptionalPrimeContribution
    (H m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ l ∈ Finset.Ico 1 H, taoExceptionalShiftPrimeWeight m' l ω

/-- The complete exceptional contribution is deterministically at most
`H log H`. -/
theorem taoExceptionalPrimeContribution_le
    {H : ℕ} (hH : 1 ≤ H) (m' : ℕ) (ω : TaoPrimeTuple) :
    taoExceptionalPrimeContribution H m' ω ≤ H * Real.log H := by
  have hterm : ∀ l ∈ Finset.Ico 1 H,
      taoExceptionalShiftPrimeWeight m' l ω ≤ Real.log H := by
    intro l hl
    have hlData := Finset.mem_Ico.mp hl
    exact (taoExceptionalShiftPrimeWeight_le_log m' hlData.1 ω).trans
      (Real.log_le_log (by exact_mod_cast hlData.1)
        (by exact_mod_cast hlData.2.le))
  calc
    taoExceptionalPrimeContribution H m' ω ≤
        ∑ _l ∈ Finset.Ico 1 H, Real.log H := by
      exact Finset.sum_le_sum hterm
    _ = ((Finset.Ico 1 H).card : ℝ) * Real.log H := by
      simp
    _ ≤ H * Real.log H := by
      have hcard : ((Finset.Ico 1 H).card : ℝ) ≤ H := by
        exact_mod_cast (show (Finset.Ico 1 H).card ≤ H by
          rw [Nat.card_Ico]
          exact Nat.sub_le H 1)
      exact mul_le_mul_of_nonneg_right hcard
        (Real.log_nonneg (by exact_mod_cast hH))

/-- At Tao's source scales the complete exceptional contribution is bounded
pointwise by `H log z`.  In particular this branch costs no probability: the
bound holds for every sampled prime tuple. -/
theorem eventually_taoExceptionalPrimeContribution_le_log_taoZ :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ H m' : ℕ, ∀ ω : TaoPrimeTuple,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
        taoExceptionalPrimeContribution H m' ω ≤
          H * Real.log (taoZ x) := by
  filter_upwards [
    eventually_const_mul_taoTypicalLengthCutoff_le_taoZ_rpow
      (C := (1 : ℝ)) (δ := (1 : ℝ)) (by norm_num) (by norm_num)] with
      x hcutoff H m' ω hH hHcutoff
  have hcutoffZ : (taoTypicalLengthCutoff x : ℝ) ≤ taoZ x := by
    simpa using hcutoff
  have hHcutoffReal : (H : ℝ) ≤ taoTypicalLengthCutoff x := by
    exact_mod_cast hHcutoff
  have hHZ : (H : ℝ) ≤ taoZ x := by
    exact hHcutoffReal.trans hcutoffZ
  have hlog : Real.log (H : ℝ) ≤ Real.log (taoZ x) :=
    Real.log_le_log (by exact_mod_cast hH) hHZ
  exact (taoExceptionalPrimeContribution_le hH m' ω).trans
    (mul_le_mul_of_nonneg_left hlog (by positivity))

/-- Event that the exceptional `p ∣ l` contribution exceeds its deterministic
source-scale bound. -/
def TaoExceptionalPrimeLargeEvent
    (x H m' : ℕ) (ω : TaoPrimeTuple) : Prop :=
  H * Real.log (taoZ x) < taoExceptionalPrimeContribution H m' ω

/-- The exceptional-prime large event is eventually empty, uniformly in all
source-admissible interval lengths and residual factors. -/
theorem eventually_taoExceptionalPrimeLargeEvent_eq_empty :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
        {ω : TaoPrimeTuple | TaoExceptionalPrimeLargeEvent x H m' ω} = ∅ := by
  filter_upwards [
    eventually_taoExceptionalPrimeContribution_le_log_taoZ] with
      x hx H m' hH hHcutoff
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact not_lt_of_ge (hx H m' ω hH hHcutoff)

/-- Consequently the exceptional branch in Proposition 6.6 has exactly zero
probability under the independent prime-tuple law. -/
theorem eventually_measure_taoExceptionalPrimeLargeEvent_eq_zero :
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ (P : Fin 1001 → ℕ)
        (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) (H m' : ℕ),
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
        taoPrimeTupleMeasure P hP
          {ω | TaoExceptionalPrimeLargeEvent x H m' ω} = 0 := by
  filter_upwards [eventually_taoExceptionalPrimeLargeEvent_eq_empty] with
      x hx P hP H m' hH hHcutoff
  rw [hx H m' hH hHcutoff]
  exact MeasureTheory.measure_empty

end

end Tao2026

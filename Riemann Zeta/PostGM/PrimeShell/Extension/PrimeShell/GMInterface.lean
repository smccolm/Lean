import PrimeShell.ShiftKernel
import Mathlib.NumberTheory.Chebyshev

namespace PrimeShell

noncomputable section

open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide

/-- The stretched-exponential saving appearing in GM Corollary 1.4. -/
def gmDecay (X : ℕ) : ℝ :=
  Real.exp (-(Real.log X) ^ (1 / 4 : ℝ))

/-- Prime count on the integer interval `(x,x+H]`. -/
def primeIntervalCount (x H : ℕ) : ℕ :=
  ((Finset.Ioc x (x + H)).filter Nat.Prime).card

/-- Prime-indicator error at one fixed length. -/
def shortIntervalPrimeError (x H : ℕ) : ℝ :=
  (primeIntervalCount x H : ℝ) - H / Real.log x

/-- Von Mangoldt mass on `(x,x+H]`. -/
def lambdaIntervalSum (x H : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc x (x + H), ArithmeticFunction.vonMangoldt n

/-- Von Mangoldt short-interval error with the consumer's endpoints. -/
def shortIntervalLambdaError (x H : ℕ) : ℝ :=
  lambdaIntervalSum x H - H

/-- Proper-prime-power contribution in the pi-to-psi conversion. -/
def primePowerEndpointError (x H : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc x (x + H),
    (ArithmeticFunction.vonMangoldt n -
      if Nat.Prime n then Real.log n else 0)

theorem lambdaIntervalSum_eq_prime_log_add_primePowerEndpointError (x H : ℕ) :
    lambdaIntervalSum x H =
      (∑ n ∈ Finset.Ioc x (x + H),
        if Nat.Prime n then Real.log n else 0) +
      primePowerEndpointError x H := by
  unfold lambdaIntervalSum primePowerEndpointError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : Nat.Prime n <;> simp [hp]

/-- Closed-paper-interval mass, kept separate from `(x,x+H]`. -/
def closedLambdaIntervalSum (x H : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc x (x + H), ArithmeticFunction.vonMangoldt n

theorem closedLambdaIntervalSum_eq_leftEndpoint_add_open (x H : ℕ) :
    closedLambdaIntervalSum x H =
      ArithmeticFunction.vonMangoldt x + lambdaIntervalSum x H := by
  unfold closedLambdaIntervalSum lambdaIntervalSum
  rw [show Finset.Icc x (x + H) = insert x (Finset.Ioc x (x + H)) by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega]
  rw [Finset.sum_insert]
  simp

/-- Exceptional set in the published prime-count statement at fixed `H`. -/
def gmPrimeBadSet (C : ℝ) (X H : ℕ) : Finset ℕ :=
  (Finset.Icc X (2 * X)).filter fun x =>
    |shortIntervalPrimeError x H| > C * H * gmDecay X

/-- Exceptional set after the paper's partial-summation conversion to Λ. -/
def gmLambdaBadSet (C : ℝ) (X H : ℕ) : Finset ℕ :=
  (Finset.Icc X (2 * X)).filter fun x =>
    |shortIntervalLambdaError x H| > C * H * gmDecay X

/-- Outer von-Mangoldt mass of the exceptional starting points. -/
def gmExceptionalLambdaMass (C : ℝ) (X H : ℕ) : ℝ :=
  ∑ n ∈ gmLambdaBadSet C X H, ArithmeticFunction.vonMangoldt n

/-- Exact exceptional mass for the Zeta23 coefficient normalization. -/
def gmExceptionalAcoefMass (C : ℝ) (X H : ℕ) : ℝ :=
  ∑ n ∈ gmLambdaBadSet C X H, acoef n

/-- A cardinality exceptional-set estimate converts to the required outer
von-Mangoldt mass with the explicit logarithmic loss. -/
theorem gmExceptionalLambdaMass_le_card_mul_log
    (C : ℝ) {X H : ℕ} (hX : 1 ≤ X) :
    gmExceptionalLambdaMass C X H ≤
      ((gmLambdaBadSet C X H).card : ℝ) * Real.log (2 * X : ℕ) := by
  unfold gmExceptionalLambdaMass
  calc
    (∑ n ∈ gmLambdaBadSet C X H, ArithmeticFunction.vonMangoldt n) ≤
        ∑ _n ∈ gmLambdaBadSet C X H, Real.log (2 * X : ℕ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIcc : n ∈ Finset.Icc X (2 * X) :=
        (Finset.mem_filter.mp hn).1
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hX.trans (Finset.mem_Icc.mp hnIcc).1)
      have h2Xpos : (0 : ℝ) < (↑(2 * X) : ℝ) := by
        exact_mod_cast Nat.mul_pos (by omega) (lt_of_lt_of_le Nat.zero_lt_one hX)
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hnpos) (Set.mem_Ioi.mpr h2Xpos)
          (by exact_mod_cast (Finset.mem_Icc.mp hnIcc).2))
    _ = ((gmLambdaBadSet C X H).card : ℝ) * Real.log (2 * X : ℕ) := by
      simp

/-- The same conversion with the exact Zeta23 normalization
`acoef n = Λ(n)/sqrt(n)`. -/
theorem gmExceptionalAcoefMass_le_card_mul_log_div_sqrt
    (C : ℝ) {X H : ℕ} (hX : 1 ≤ X) :
    gmExceptionalAcoefMass C X H ≤
      ((gmLambdaBadSet C X H).card : ℝ) *
        (Real.log (2 * X : ℕ) / Real.sqrt X) := by
  unfold gmExceptionalAcoefMass
  calc
    (∑ n ∈ gmLambdaBadSet C X H, acoef n) ≤
        ∑ _n ∈ gmLambdaBadSet C X H,
          Real.log (2 * X : ℕ) / Real.sqrt X := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIcc : n ∈ Finset.Icc X (2 * X) :=
        (Finset.mem_filter.mp hn).1
      have hXpos : (0 : ℝ) < X := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hX
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hX.trans (Finset.mem_Icc.mp hnIcc).1)
      have h2Xpos : (0 : ℝ) < (↑(2 * X) : ℝ) := by positivity
      have hlog : Real.log n ≤ Real.log (2 * X : ℕ) :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hnpos) (Set.mem_Ioi.mpr h2Xpos)
          (by exact_mod_cast (Finset.mem_Icc.mp hnIcc).2)
      have hsqrt : Real.sqrt X ≤ Real.sqrt n :=
        Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.mp hnIcc).1)
      unfold acoef
      calc
        ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
            Real.log n / Real.sqrt n :=
          div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
            (Real.sqrt_nonneg _)
        _ ≤ Real.log n / Real.sqrt X := by
          exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg n)
            (Real.sqrt_pos.2 hXpos) hsqrt
        _ ≤ Real.log (2 * X : ℕ) / Real.sqrt X :=
          div_le_div_of_nonneg_right hlog (Real.sqrt_nonneg _)
    _ = ((gmLambdaBadSet C X H).card : ℝ) *
          (Real.log (2 * X : ℕ) / Real.sqrt X) := by
      simp

/-- Literal finite fixed-length pi statement of GM Corollary 1.4.  This is a
specification, not an axiom or a theorem claimed in this extension. -/
def GMCorollary14PiFinite : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ X H : ℕ,
    X₀ ≤ X → 2 ≤ X →
    (X : ℝ) ^ (2 / 15 + ε) ≤ H →
    (H : ℝ) ≤ (X : ℝ) ^ (99 / 100 : ℝ) →
    ((gmPrimeBadSet C X H).card : ℝ) ≤ C * X * gmDecay X

/-- Narrow fixed-length Λ interface justified only after partial summation,
prime-power control, and endpoint conversion. -/
def GMCorollary14LambdaFinite : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ X H : ℕ,
    X₀ ≤ X → 2 ≤ X →
    (X : ℝ) ^ (2 / 15 + ε) ≤ H →
    (H : ℝ) ≤ (X : ℝ) ^ (99 / 100 : ℝ) →
    ((gmLambdaBadSet C X H).card : ℝ) ≤ C * X * gmDecay X

/-- Union cost for an explicitly supplied finite family of lengths. -/
def gmSimultaneousLambdaBadSet
    (C : ℝ) (X : ℕ) (lengths : Finset ℕ) : Finset ℕ :=
  lengths.biUnion fun H => gmLambdaBadSet C X H

theorem card_gmSimultaneousLambdaBadSet_le_sum_cards
    (C : ℝ) (X : ℕ) (lengths : Finset ℕ) :
    (gmSimultaneousLambdaBadSet C X lengths).card ≤
      ∑ H ∈ lengths, (gmLambdaBadSet C X H).card := by
  unfold gmSimultaneousLambdaBadSet
  exact Finset.card_biUnion_le

/-- Raw un-normalized von Mangoldt correlation at one positive shift. -/
def rawDyadicLambdaCorrelation (N h : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    if n + h ∈ Finset.Ioc N (2 * N) then
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + h)
    else 0

/-- Cumulative raw correlation prefix. -/
def rawDyadicLambdaPrefix (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, rawDyadicLambdaCorrelation N h

/-- Exact shift-to-short-interval identity with the right edge retained. -/
theorem rawDyadicLambdaPrefix_eq_weighted_shortIntervals (N H : ℕ) :
    rawDyadicLambdaPrefix N H =
      ∑ n ∈ Finset.Ioc N (2 * N), ArithmeticFunction.vonMangoldt n *
        (∑ h ∈ Finset.Icc 1 H,
          if n + h ∈ Finset.Ioc N (2 * N) then
            ArithmeticFunction.vonMangoldt (n + h) else 0) := by
  unfold rawDyadicLambdaPrefix rawDyadicLambdaCorrelation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N) <;> simp [hmem]

/-- Conjunction exposing all published dependencies used in GM Section 13.2.
It is a bookkeeping connective, not an assertion that the inputs are proved. -/
def GMSection132Dependencies
    (piToPsiPartialSummation properPrimePowerBound explicitFormulaTruncation
      nearOneLogarithmicDensity vinogradovKorobovZeroFreeRegion
      shortIntervalMeanSquare : Prop) : Prop :=
  piToPsiPartialSummation ∧ properPrimePowerBound ∧ explicitFormulaTruncation ∧
    nearOneLogarithmicDensity ∧ vinogradovKorobovZeroFreeRegion ∧
    shortIntervalMeanSquare

end

end PrimeShell

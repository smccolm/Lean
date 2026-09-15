import Tao2026.SylvesterSchurSmallLengths

/-!
# A factorial start threshold for Sylvester--Schur

The coarse fixed-length threshold `H^H + 1` is enough to make the residual
rectangle finite, but it is much larger than the classical factorial cutoff.
This file proves the sharper criterion independently from the elementary
factorization envelope already developed in `VeryBadIntervals`.

For the interval `N+1, ..., N+H`, put `m = N+1` and
`r = card ((H+1).primesBelow)`.  If all prime factors of the relevant
binomial coefficient were at most `H`, its size would be at most
`(N+H)^r`.  On the other hand,

`m^H <= m.ascFactorial H = H! * choose (N+H) H`.

Since `N+H <= 2m`, the strict gap
`H! * 2^r < m^(H-r)` forces a prime factor larger than `H`.  The elementary
bound `r < H` then yields the explicit cutoff `H! * 2^(H-1) + 1`.
-/

namespace Tao2026

/-- The factorial/exponent gap that forces the binomial coefficient to have a
prime divisor larger than the interval length. -/
theorem choose_growth_of_factorial_exponent_gap
    {N H r : ℕ} (hHN : H < N) (hrH : r < H)
    (hcard : (H + 1).primesBelow.card ≤ r)
    (hgap : H.factorial * 2 ^ r < (N + 1) ^ (H - r)) :
    (N + H) ^ (H + 1).primesBelow.card < (N + H).choose H := by
  have hHle : H ≤ N + H := by omega
  have hsumPos : 0 < N + H := by omega
  have hstartPos : 0 < N + 1 := by omega
  have htop : N + H ≤ 2 * (N + 1) := by omega
  by_contra hnot
  have hchoose : (N + H).choose H ≤ (N + H) ^ r := by
    exact (Nat.le_of_not_gt hnot).trans
      (Nat.pow_le_pow_right hsumPos hcard)
  have hlower : (N + 1) ^ H ≤ H.factorial * (N + H).choose H := by
    simpa [Nat.ascFactorial_eq_factorial_mul_choose] using
      Nat.pow_succ_le_ascFactorial (N + 1) H
  have hupper :
      H.factorial * (N + H).choose H ≤
        (H.factorial * 2 ^ r) * (N + 1) ^ r := by
    calc
      H.factorial * (N + H).choose H ≤ H.factorial * (N + H) ^ r :=
        Nat.mul_le_mul_left H.factorial hchoose
      _ ≤ H.factorial * (2 * (N + 1)) ^ r :=
        Nat.mul_le_mul_left H.factorial (Nat.pow_le_pow_left htop r)
      _ = (H.factorial * 2 ^ r) * (N + 1) ^ r := by
        rw [mul_pow]
        ring
  have hstrict :
      (H.factorial * 2 ^ r) * (N + 1) ^ r < (N + 1) ^ H := by
    calc
      (H.factorial * 2 ^ r) * (N + 1) ^ r <
          (N + 1) ^ (H - r) * (N + 1) ^ r :=
        Nat.mul_lt_mul_of_pos_right hgap (Nat.pow_pos hstartPos)
      _ = (N + 1) ^ H := by
        rw [← pow_add]
        congr 1
        omega
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

/-- A factorial/exponent gap supplies a prime larger than `H` dividing the
consecutive product. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_factorial_exponent_gap
    {N H r : ℕ} (hH : 1 ≤ H) (hHN : H < N) (hrH : r < H)
    (hcard : (H + 1).primesBelow.card ≤ r)
    (hgap : H.factorial * 2 ^ r < (N + 1) ^ (H - r)) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  have hgrowth := choose_growth_of_factorial_exponent_gap
    hHN hrH hcard hgap
  obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
    exists_large_prime_dvd_choose_of_pow_card_lt
      (show H ≤ N + H by omega) (by omega) hgrowth
  refine ⟨p, hpPrime, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- The sharp threshold delivered by the elementary factorization envelope,
retaining the exact number of primes at most `H`. -/
def sylvesterSchurPrimeCountFactorialThreshold (H : ℕ) : ℕ :=
  H.factorial * 2 ^ (H + 1).primesBelow.card + 1

/-- Once the first interval term reaches the exact prime-count factorial
threshold, the Sylvester--Schur prime exists. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
    {N H : ℕ} (hH : 1 ≤ H) (hHN : H < N)
    (hthreshold : sylvesterSchurPrimeCountFactorialThreshold H ≤ N + 1) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  let r := (H + 1).primesBelow.card
  have hrH : r < H := by
    dsimp [r]
    rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self hH
  have hcoefficient : H.factorial * 2 ^ r < N + 1 := by
    calc
      H.factorial * 2 ^ r <
          sylvesterSchurPrimeCountFactorialThreshold H := by
        simp [r, sylvesterSchurPrimeCountFactorialThreshold]
      _ ≤ N + 1 := hthreshold
  have hstartPow : N + 1 ≤ (N + 1) ^ (H - r) := by
    exact le_self_pow (by omega) (by omega)
  exact exists_large_prime_dvd_consecutiveProduct_of_factorial_exponent_gap
    hH hHN hrH (by rfl) (hcoefficient.trans_le hstartPow)

/-- The classical elementary fixed-length start threshold. -/
def sylvesterSchurFactorialThreshold (H : ℕ) : ℕ :=
  H.factorial * 2 ^ (H - 1) + 1

theorem sylvesterSchurPrimeCountFactorialThreshold_le (H : ℕ) (hH : 1 ≤ H) :
    sylvesterSchurPrimeCountFactorialThreshold H ≤
      sylvesterSchurFactorialThreshold H := by
  have hcard : (H + 1).primesBelow.card ≤ H - 1 := by
    rw [card_primesBelow_succ_eq_primeCounting]
    have := primeCounting_lt_self hH
    omega
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left H.factorial
      (Nat.pow_le_pow_right (by omega) hcard)) 1

/-- Once the first interval term reaches the factorial threshold, the
Sylvester--Schur prime exists. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_factorialThreshold_le
    {N H : ℕ} (hH : 1 ≤ H) (hHN : H < N)
    (hthreshold : sylvesterSchurFactorialThreshold H ≤ N + 1) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  exact
    exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
      hH hHN
        ((sylvesterSchurPrimeCountFactorialThreshold_le H hH).trans hthreshold)

/-- The smallest finite rectangle produced by this factorial argument. -/
def SylvesterSchurPrimeCountFactorialFiniteRectangle (B : ℕ) : Prop :=
  ∀ {N H : ℕ}, 1 ≤ H → H < B → H < N →
    N + 1 < sylvesterSchurPrimeCountFactorialThreshold H →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

theorem sylvesterSchurBelow_of_primeCountFactorialFiniteRectangle {B : ℕ}
    (hrect : SylvesterSchurPrimeCountFactorialFiniteRectangle B) :
    SylvesterSchurBelow B := by
  intro N H hH hHB hHN
  by_cases hsmall : N + 1 < sylvesterSchurPrimeCountFactorialThreshold H
  · exact hrect hH hHB hHN hsmall
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
        hH hHN (Nat.le_of_not_gt hsmall)

/-- The sharper genuinely finite residual rectangle obtained from the
factorial threshold. -/
def SylvesterSchurFactorialFiniteRectangle (B : ℕ) : Prop :=
  ∀ {N H : ℕ}, 1 ≤ H → H < B → H < N →
    N + 1 < sylvesterSchurFactorialThreshold H →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- A proof on the factorial rectangle supplies every start for every length
below `B`. -/
theorem sylvesterSchurBelow_of_factorialFiniteRectangle {B : ℕ}
    (hrect : SylvesterSchurFactorialFiniteRectangle B) :
    SylvesterSchurBelow B := by
  intro N H hH hHB hHN
  by_cases hsmall : N + 1 < sylvesterSchurFactorialThreshold H
  · exact hrect hH hHB hHN hsmall
  · exact exists_large_prime_dvd_consecutiveProduct_of_factorialThreshold_le
      hH hHN (Nat.le_of_not_gt hsmall)

/-- Only the sharper factorial rectangle remains after combining it with the
already proved uniform large-length tail. -/
theorem exists_sylvesterSchur_factorialFiniteRectangleReduction :
    ∃ B : ℕ, SylvesterSchurFactorialFiniteRectangle B →
      SylvesterSchurConclusion := by
  obtain ⟨B, htail⟩ := exists_sylvesterSchur_tailCutoff
  refine ⟨B, fun hrect => ?_⟩
  exact sylvesterSchurConclusion_of_below_of_tailCutoff
    (sylvesterSchurBelow_of_factorialFiniteRectangle hrect) htail

/-- The unrestricted conclusion is reduced to the exact-prime-count factorial
rectangle, a subset of the classical factorial rectangle. -/
theorem exists_sylvesterSchur_primeCountFactorialFiniteRectangleReduction :
    ∃ B : ℕ, SylvesterSchurPrimeCountFactorialFiniteRectangle B →
      SylvesterSchurConclusion := by
  obtain ⟨B, htail⟩ := exists_sylvesterSchur_tailCutoff
  refine ⟨B, fun hrect => ?_⟩
  exact sylvesterSchurConclusion_of_below_of_tailCutoff
    (sylvesterSchurBelow_of_primeCountFactorialFiniteRectangle hrect) htail

end Tao2026

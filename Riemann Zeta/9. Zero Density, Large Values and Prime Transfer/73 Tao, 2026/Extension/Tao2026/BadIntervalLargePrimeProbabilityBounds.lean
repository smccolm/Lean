import Tao2026.BadIntervalLargePrimeCrudeSource
import Tao2026.BadIntervalLargePrimeNonprincipal
import Tao2026.BadIntervalLargePrimeProductCollision

/-!
# Literal improved probability bounds for Propositions 6.7 and 6.8

The character modules bound a primitive residue fiber.  This module transfers
those estimates to the actual single- and joint-divisibility events.  The
events may be empty; that branch is harmless for the upper bounds needed in
the mean and covariance sums.  In the nonempty branch, the previously proved
event-to-primitive-fiber equivalences give the result directly.
-/

namespace Tao2026

open MeasureTheory
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- Complete explicit error accompanying the one-prime main term. -/
def taoLargePrimeImprovedError (P : Fin 1001 → ℕ) (p : ℕ) : ℝ :=
  (p.totient : ℝ)⁻¹ *
    ((∑ j : Fin 1001,
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) +
      (p.totient : ℝ) *
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (P j : ℝ) ^ (-(8 : ℝ)))

/-- Complete explicit error accompanying the product-modulus main term,
including both principal collisions and change-level collisions. -/
def taoLargePrimeJointImprovedError
    (P : Fin 1001 → ℕ) (p q : ℕ) : ℝ :=
  ((p * q).totient : ℝ)⁻¹ *
    ((2 * ∑ j : Fin 1001,
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) +
      (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) *
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              (P j : ℝ) ^ (-(8 : ℝ)) +
          ((p * q).totient : ℝ) *
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                (1000 : ℕ)))

/-- If the fixed remainder is invertible modulo `p`, some unrestricted prime
tuple realizes any one shifted divisibility event.  The tuple is used only to
rule out the empty branch of the event-to-residue-fiber dichotomy; membership
in the sampled support is neither asserted nor needed. -/
theorem taoLargePrimeDivisibilityEvent_nonempty_of_coprime_remainder
    {m' : ℕ} (a : ℕ × ℕ) (hp : Nat.Prime a.2)
    (hm : Nat.Coprime m' a.2) :
    ∃ w : TaoPrimeTuple, TaoLargePrimeDivisibilityEvent m' a w := by
  letI : NeZero a.2 := ⟨hp.ne_zero⟩
  rcases (ZMod.isUnit_iff_coprime m' a.2).2 hm with ⟨u, hu⟩
  let z : ZMod a.2 := (↑(u⁻¹) : ZMod a.2) * (-(a.1 : ZMod a.2))
  let w : TaoPrimeTuple := fun k => if k = (1 : Fin 1001) then z.val else 1
  refine ⟨w, ?_⟩
  have hwstart : taoPrimeTupleStart m' w = z.val * m' := by
    simp [taoPrimeTupleStart, taoPrimeTupleTailProduct, w,
      Finset.prod_ite_eq', z]
  rw [TaoLargePrimeDivisibilityEvent, hwstart]
  apply Nat.modEq_zero_iff_dvd.mp
  apply (ZMod.natCast_eq_natCast_iff (z.val * m' + a.1) 0 a.2).mp
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [← hu]
  have huz : (↑(u⁻¹) : ZMod a.2) * (u : ZMod a.2) = 1 := by simp
  rw [show (↑(u⁻¹) : ZMod a.2) * (-(a.1 : ZMod a.2)) * (u : ZMod a.2) =
      -(a.1 : ZMod a.2) by
    calc
      (↑(u⁻¹) : ZMod a.2) * (-(a.1 : ZMod a.2)) * (u : ZMod a.2) =
          -(a.1 : ZMod a.2) *
            ((↑(u⁻¹) : ZMod a.2) * (u : ZMod a.2)) := by ring
      _ = -(a.1 : ZMod a.2) := by rw [huz, mul_one]]
  simp

/-- Full absolute-deviation form of Proposition 6.7(ii) outside the
exceptional conductor set.  Coprimality of the remainder rules out the empty
event branch. -/
theorem abs_taoLargePrimeProbability_sub_main_le_unexceptionalError
    {D : Finset ℕ} {m' : ℕ} (a : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hpD : a.2 ∈ D)
    (hpl : ¬a.2 ∣ a.1) (hm : Nat.Coprime m' a.2)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpExceptional : a.2 ∉ taoLargePrimeExceptionalConductorsFor D P) :
    |taoLargePrimeProbability P hP m' a - 1 / (a.2.totient : ℝ)| ≤
      taoLargePrimeImprovedError P a.2 := by
  rcases taoLargePrimeDivisibilityEvent_empty_or_primitiveResidueClass
    hp hpl with hempty | ⟨r, hr, hset⟩
  · obtain ⟨w, hw⟩ :=
      taoLargePrimeDivisibilityEvent_nonempty_of_coprime_remainder a hp hm
    have hwEmpty : w ∈ (∅ : Set TaoPrimeTuple) := by
      rw [← hempty]
      exact hw
    simp at hwEmpty
  · have hnorm :=
      primitiveResidueFiber_probability_sub_main_norm_le_prime_unexceptional
        hp hpD hr hm P hP hpExceptional
    rw [taoLargePrimeProbability, hset]
    have heq :
        (((taoPrimeTupleMeasure P hP).real
              {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} : ℝ) : ℂ) -
            (1 / (a.2.totient : ℂ)) =
          (((taoPrimeTupleMeasure P hP).real
              {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} -
            1 / (a.2.totient : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.norm_real] at hnorm
    simpa [taoLargePrimeImprovedError, one_div] using hnorm

/-- Literal upper half of Proposition 6.7(ii) outside the exceptional
conductor set.  The bound also covers the case in which the divisibility event
is empty. -/
theorem taoLargePrimeProbability_le_main_add_unexceptionalError
    {D : Finset ℕ} {m' : ℕ} (a : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hpD : a.2 ∈ D)
    (hpl : ¬a.2 ∣ a.1) (hm : Nat.Coprime m' a.2)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpExceptional : a.2 ∉ taoLargePrimeExceptionalConductorsFor D P) :
    taoLargePrimeProbability P hP m' a ≤
      1 / (a.2.totient : ℝ) + taoLargePrimeImprovedError P a.2 := by
  rcases taoLargePrimeDivisibilityEvent_empty_or_primitiveResidueClass
    hp hpl with hempty | ⟨r, hr, hset⟩
  · rw [taoLargePrimeProbability, hempty, measureReal_empty]
    unfold taoLargePrimeImprovedError
    positivity
  · have hnorm :=
      primitiveResidueFiber_probability_sub_main_norm_le_prime_unexceptional
        hp hpD hr hm P hP hpExceptional
    rw [taoLargePrimeProbability, hset]
    have hreal :
        |(taoPrimeTupleMeasure P hP).real
              {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} -
            1 / (a.2.totient : ℝ)| ≤
          taoLargePrimeImprovedError P a.2 := by
      have heq :
          (((taoPrimeTupleMeasure P hP).real
                {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} : ℝ) : ℂ) -
              (1 / (a.2.totient : ℂ)) =
            (((taoPrimeTupleMeasure P hP).real
                {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} -
              1 / (a.2.totient : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_real] at hnorm
      simpa [taoLargePrimeImprovedError, one_div] using hnorm
    nlinarith [le_trans (le_abs_self
      ((taoPrimeTupleMeasure P hP).real
          {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} -
        1 / (a.2.totient : ℝ))) hreal]

/-- Literal upper half of Proposition 6.8(ii) outside all nontrivial
exceptional divisor conductors.  This includes the empty joint-event branch. -/
theorem taoLargePrimeJointProbability_le_main_add_unexceptionalError
    {m' : ℕ} (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1)
    (hm : Nat.Coprime m' (a.2 * b.2))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hExceptional : ∀ d ∈ (a.2 * b.2).divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsFor
        ((a.2 * b.2).divisors.erase 1) P) :
    taoLargePrimeJointProbability P hP m' a b ≤
      1 / ((a.2 * b.2).totient : ℝ) +
        taoLargePrimeJointImprovedError P a.2 b.2 := by
  rcases taoLargePrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
    hp hq hpq hpa hqb with hempty | ⟨r, hr, hset⟩
  · rw [taoLargePrimeJointProbability, hempty, measureReal_empty]
    unfold taoLargePrimeJointImprovedError
    positivity
  · have hnorm :=
      primitiveResidueFiber_probability_sub_main_norm_le_prime_mul_unexceptional
        hp hq hr hm P hP hExceptional
    rw [taoLargePrimeJointProbability, hset]
    have hreal :
        |(taoPrimeTupleMeasure P hP).real
              {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} -
            1 / ((a.2 * b.2).totient : ℝ)| ≤
          taoLargePrimeJointImprovedError P a.2 b.2 := by
      have heq :
          (((taoPrimeTupleMeasure P hP).real
                {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} : ℝ) : ℂ) -
              (1 / ((a.2 * b.2).totient : ℂ)) =
            (((taoPrimeTupleMeasure P hP).real
                {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} -
              1 / ((a.2 * b.2).totient : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_real] at hnorm
      simpa [taoLargePrimeJointImprovedError, one_div] using hnorm
    nlinarith [le_trans (le_abs_self
      ((taoPrimeTupleMeasure P hP).real
          {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} -
        1 / ((a.2 * b.2).totient : ℝ))) hreal]

/-- An elementary one-sided covariance estimate from a joint upper bound and
two absolute marginal errors.  It is stated separately so that the analytic
input and the probability algebra remain auditable. -/
theorem sub_mul_le_of_abs_sub_le
    {J Pa Pb ma mb Ea Eb Ej : ℝ}
    (hJ : J ≤ ma * mb + Ej)
    (ha : |Pa - ma| ≤ Ea) (hb : |Pb - mb| ≤ Eb)
    (hma : 0 ≤ ma) (hmb : 0 ≤ mb) (hEa : 0 ≤ Ea) :
    J - Pa * Pb ≤ Ej + ma * Eb + mb * Ea + Ea * Eb := by
  have haLower : -Ea ≤ Pa - ma := neg_le_of_abs_le ha
  have hbLower : -Eb ≤ Pb - mb := neg_le_of_abs_le hb
  have hproductAbs : |(Pa - ma) * (Pb - mb)| ≤ Ea * Eb := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hEa
  have hproductLower : -(Ea * Eb) ≤ (Pa - ma) * (Pb - mb) :=
    neg_le_of_abs_le hproductAbs
  nlinarith

/-- Proposition 6.8(ii) in the covariance form used by the second-moment
argument.  The exceptional-conductor hypothesis for the product modulus also
supplies the two prime-modulus hypotheses because both primes are nontrivial
divisors of their product. -/
theorem taoLargePrimeCovariance_le_unexceptionalErrors
    {m' : ℕ} (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1)
    (hm : Nat.Coprime m' (a.2 * b.2))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hExceptional : ∀ d ∈ (a.2 * b.2).divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsFor
        ((a.2 * b.2).divisors.erase 1) P) :
    taoLargePrimeCovariance P hP m' a b ≤
      taoLargePrimeJointImprovedError P a.2 b.2 +
        (1 / (a.2.totient : ℝ)) * taoLargePrimeImprovedError P b.2 +
        (1 / (b.2.totient : ℝ)) * taoLargePrimeImprovedError P a.2 +
        taoLargePrimeImprovedError P a.2 *
          taoLargePrimeImprovedError P b.2 := by
  have hpD : a.2 ∈ (a.2 * b.2).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hp.ne_one]
  have hqD : b.2 ∈ (a.2 * b.2).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hq.ne_one]
  have hmParts : Nat.Coprime m' a.2 ∧ Nat.Coprime m' b.2 :=
    Nat.coprime_mul_iff_right.mp hm
  have hpqCoprime : Nat.Coprime a.2 b.2 :=
    (Nat.coprime_primes hp hq).2 hpq
  have htotient : (a.2 * b.2).totient = a.2.totient * b.2.totient :=
    Nat.totient_mul hpqCoprime
  have hmain :
      1 / ((a.2 * b.2).totient : ℝ) =
        (1 / (a.2.totient : ℝ)) * (1 / (b.2.totient : ℝ)) := by
    rw [htotient]
    push_cast
    simp only [one_div, mul_inv]
  have hJ := taoLargePrimeJointProbability_le_main_add_unexceptionalError
    a b hp hq hpq hpa hqb hm P hP hExceptional
  rw [hmain] at hJ
  have ha := abs_taoLargePrimeProbability_sub_main_le_unexceptionalError
    a hp hpD hpa hmParts.1 P hP (hExceptional a.2 hpD)
  have hb := abs_taoLargePrimeProbability_sub_main_le_unexceptionalError
    b hq hqD hqb hmParts.2 P hP (hExceptional b.2 hqD)
  rw [taoLargePrimeCovariance]
  apply sub_mul_le_of_abs_sub_le hJ ha hb
  · positivity
  · positivity
  · unfold taoLargePrimeImprovedError
    positivity

end

end Tao2026

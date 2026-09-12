import Mathlib.NumberTheory.SmoothNumbers
import Tao2026.Counting

/-!
# Source-facing smooth numbers

Mathlib's `Nat.smoothNumbers k` uses the strict convention that every prime
factor is less than `k`. Tao calls a positive natural `y`-smooth when every
prime factor is at most `y`, so the source-facing predicate below uses
`Nat.smoothNumbers (y + 1)`.

This file begins the exact one-term-set calculation preceding Proposition 2.1.
In particular, it proves the unique `p² m` representation of a member of
`B¹`; no smooth-number asymptotic is assumed here.
-/

namespace Tao2026

/-- Tao's inclusive convention: `n` is positive and every prime factor of
`n` is at most `y`. -/
def IsSmooth (n y : ℕ) : Prop := n ∈ Nat.smoothNumbers (y + 1)

theorem isSmooth_iff {n y : ℕ} :
    IsSmooth n y ↔ n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ y := by
  constructor
  · intro hn
    refine ⟨Nat.ne_zero_of_mem_smoothNumbers hn, ?_⟩
    intro p hp hpdvd
    exact Nat.lt_add_one_iff.mp (Nat.mem_smoothNumbers'.mp hn p hp hpdvd)
  · rintro ⟨_, hn⟩
    rw [IsSmooth, Nat.mem_smoothNumbers']
    intro p hp hpdvd
    exact Nat.lt_add_one_iff.mpr (hn p hp hpdvd)

/-- The exact finite smooth-number counting function used by the integral
version of Tao's identity for `B¹`. -/
def psiNat (x y : ℕ) : ℕ := (Nat.smoothNumbersUpTo x (y + 1)).card

@[simp]
theorem psiNat_eq_card (x y : ℕ) :
    psiNat x y = (Nat.smoothNumbersUpTo x (y + 1)).card := rfl

theorem mem_smoothNumbersUpTo_source {x y n : ℕ} :
    n ∈ Nat.smoothNumbersUpTo x (y + 1) ↔ n ≤ x ∧ IsSmooth n y := by
  simp [IsSmooth, Nat.mem_smoothNumbersUpTo]

/-! ## Exact largest-prime-factor recurrence -/

/-- The collision-free representation family behind the Buchstab recurrence:
the first coordinate is the largest prime factor and the second is the
remaining smooth cofactor. -/
noncomputable def smoothLargestPrimeRepresentations (X y : ℕ) :
    Finset (Σ _p : ℕ, ℕ) := by
  classical
  exact ((Finset.Icc 2 (min X y)).filter Nat.Prime).sigma fun p =>
    Nat.smoothNumbersUpTo (X / p) (p + 1)

/-- The natural represented by a largest-prime/cofactor pair. -/
def smoothLargestPrimeRepresentationValue (r : Σ _p : ℕ, ℕ) : ℕ :=
  r.1 * r.2

theorem mem_smoothLargestPrimeRepresentations_iff
    {X y : ℕ} {r : Σ _p : ℕ, ℕ} :
    r ∈ smoothLargestPrimeRepresentations X y ↔
      r.1.Prime ∧ 2 ≤ r.1 ∧ r.1 ≤ X ∧ r.1 ≤ y ∧
        r.2 ≤ X / r.1 ∧ IsSmooth r.2 r.1 := by
  classical
  simp [smoothLargestPrimeRepresentations, mem_smoothNumbersUpTo_source,
    and_left_comm, and_assoc]

/-- A represented number has precisely the declared largest prime factor. -/
theorem largestPrimeFactor_smoothLargestPrimeRepresentation
    {p m : ℕ} (hp : p.Prime) (hm : IsSmooth m p) :
    largestPrimeFactor (p * m) = some p := by
  have hm0 : m ≠ 0 := (isSmooth_iff.mp hm).1
  have hprod0 : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm0
  rw [largestPrimeFactor_eq_some_iff]
  constructor
  · exact hp.mem_primeFactors (dvd_mul_right p m) hprod0
  · intro q hqmem
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqdiv : q ∣ p * m := Nat.dvd_of_mem_primeFactors hqmem
    rcases hqprime.dvd_mul.mp hqdiv with hqp | hqm
    · exact ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqp).le
    · exact (isSmooth_iff.mp hm).2 q hqprime hqm

/-- Forgetting the representation gives exactly the non-unit smooth numbers
up to `X`. -/
theorem image_smoothLargestPrimeRepresentations (X y : ℕ) :
    (smoothLargestPrimeRepresentations X y).image
        smoothLargestPrimeRepresentationValue =
      (Nat.smoothNumbersUpTo X (y + 1)).erase 1 := by
  classical
  ext n
  constructor
  · intro hn
    rw [Finset.mem_image] at hn
    rcases hn with ⟨⟨p, m⟩, hpm, rfl⟩
    have hpm' := mem_smoothLargestPrimeRepresentations_iff.mp hpm
    have hm0 : m ≠ 0 := (isSmooth_iff.mp hpm'.2.2.2.2.2).1
    have hp0 : p ≠ 0 := hpm'.1.ne_zero
    have hle : p * m ≤ X := by
      have := (Nat.le_div_iff_mul_le hpm'.1.pos).mp hpm'.2.2.2.2.1
      simpa only [mul_comm] using this
    have hsmooth : IsSmooth (p * m) y := by
      rw [isSmooth_iff]
      refine ⟨mul_ne_zero hp0 hm0, ?_⟩
      intro q hq hqdiv
      rcases hq.dvd_mul.mp hqdiv with hqp | hqm
      · have hqpEq : q = p := (Nat.prime_dvd_prime_iff_eq hq hpm'.1).mp hqp
        exact hqpEq ▸ hpm'.2.2.2.1
      · exact (isSmooth_iff.mp hpm'.2.2.2.2.2).2 q hq hqm |>.trans
          hpm'.2.2.2.1
    have hneOne : p * m ≠ 1 := by
      intro hone
      have hnone : largestPrimeFactor (p * m) = none :=
        largestPrimeFactor_eq_none_iff.mpr (Or.inr hone)
      rw [largestPrimeFactor_smoothLargestPrimeRepresentation hpm'.1
        hpm'.2.2.2.2.2] at hnone
      simp at hnone
    rw [Finset.mem_erase, mem_smoothNumbersUpTo_source]
    exact ⟨hneOne, hle, hsmooth⟩
  · intro hn
    rw [Finset.mem_erase, mem_smoothNumbersUpTo_source] at hn
    rcases hn with ⟨hnOne, hnX, hnSmooth⟩
    have hn0 : n ≠ 0 := (isSmooth_iff.mp hnSmooth).1
    have hlpfNotNone : largestPrimeFactor n ≠ none := by
      intro hlpf
      rcases largestPrimeFactor_eq_none_iff.mp hlpf with hnZero | hnEqOne
      · exact hn0 hnZero
      · exact hnOne hnEqOne
    cases hlpf : largestPrimeFactor n with
    | none => exact (hlpfNotNone hlpf).elim
    | some p =>
        have hpData := largestPrimeFactor_eq_some_iff.mp hlpf
        have hp : p.Prime := Nat.prime_of_mem_primeFactors hpData.1
        have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpData.1
        have hpLeN : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpDvd
        have hpLeX : p ≤ X := hpLeN.trans hnX
        have hpLeY : p ≤ y := (isSmooth_iff.mp hnSmooth).2 p hp hpDvd
        have hmLe : n / p ≤ X / p := Nat.div_le_div_right hnX
        have hdecomp : p * (n / p) = n := Nat.mul_div_cancel' hpDvd
        have hmSmooth : IsSmooth (n / p) p := by
          rw [isSmooth_iff]
          constructor
          · exact Nat.ne_of_gt (Nat.div_pos hpLeN hp.pos)
          · intro q hq hqdiv
            have hqDvdN : q ∣ n := by
              rw [← hdecomp]
              exact dvd_mul_of_dvd_right hqdiv p
            exact hpData.2 q (hq.mem_primeFactors hqDvdN hn0)
        rw [Finset.mem_image]
        refine ⟨⟨p, n / p⟩, ?_, hdecomp⟩
        exact mem_smoothLargestPrimeRepresentations_iff.mpr
          ⟨hp, hp.two_le, hpLeX, hpLeY, hmLe, hmSmooth⟩

/-- The representation-value map is injective because the first coordinate
is the largest prime factor, after which cancellation recovers the cofactor. -/
theorem injOn_smoothLargestPrimeRepresentationValue (X y : ℕ) :
    Set.InjOn smoothLargestPrimeRepresentationValue
      (smoothLargestPrimeRepresentations X y) := by
  rintro ⟨p, m⟩ hpm ⟨q, k⟩ hqk heq
  have hpm' := mem_smoothLargestPrimeRepresentations_iff.mp hpm
  have hqk' := mem_smoothLargestPrimeRepresentations_iff.mp hqk
  change p * m = q * k at heq
  have hpq : p = q := by
    have hlp := largestPrimeFactor_smoothLargestPrimeRepresentation
      hpm'.1 hpm'.2.2.2.2.2
    have hlq := largestPrimeFactor_smoothLargestPrimeRepresentation
      hqk'.1 hqk'.2.2.2.2.2
    exact Option.some.inj (hlp.symm.trans ((congrArg largestPrimeFactor heq).trans hlq))
  subst q
  have hmk : m = k := Nat.eq_of_mul_eq_mul_left hpm'.1.pos heq
  subst k
  rfl

/-- Cardinality of the largest-prime representation family. -/
theorem card_smoothLargestPrimeRepresentations (X y : ℕ) :
    (smoothLargestPrimeRepresentations X y).card =
      ∑ p ∈ (Finset.Icc 2 (min X y)).filter Nat.Prime,
        psiNat (X / p) p := by
  classical
  rw [smoothLargestPrimeRepresentations, Finset.card_sigma]
  rfl

/-- Exact largest-prime-factor (Buchstab) recurrence for the source-facing
smooth-number counting function. -/
theorem psiNat_eq_one_add_sum_largestPrime {X y : ℕ} (hX : 1 ≤ X) :
    psiNat X y = 1 +
      ∑ p ∈ (Finset.Icc 2 (min X y)).filter Nat.Prime,
        psiNat (X / p) p := by
  classical
  have hone : 1 ∈ Nat.smoothNumbersUpTo X (y + 1) := by
    rw [mem_smoothNumbersUpTo_source]
    refine ⟨hX, ?_⟩
    rw [isSmooth_iff]
    exact ⟨one_ne_zero, fun p hp hpdvd => (hp.not_dvd_one hpdvd).elim⟩
  have herase : ((Nat.smoothNumbersUpTo X (y + 1)).erase 1).card =
      ∑ p ∈ (Finset.Icc 2 (min X y)).filter Nat.Prime,
        psiNat (X / p) p := by
    rw [← image_smoothLargestPrimeRepresentations X y,
      Finset.card_image_iff.mpr
        (injOn_smoothLargestPrimeRepresentationValue X y),
      card_smoothLargestPrimeRepresentations]
  calc
    psiNat X y = (Nat.smoothNumbersUpTo X (y + 1)).card := rfl
    _ = ((Nat.smoothNumbersUpTo X (y + 1)).erase 1).card + 1 :=
      (Finset.card_erase_add_one hone).symm
    _ = (∑ p ∈ (Finset.Icc 2 (min X y)).filter Nat.Prime,
        psiNat (X / p) p) + 1 := by rw [herase]
    _ = 1 + ∑ p ∈ (Finset.Icc 2 (min X y)).filter Nat.Prime,
        psiNat (X / p) p := Nat.add_comm _ _

/-- The unit is counted by `Psi(X,y)` as soon as the range is nonempty. -/
theorem one_le_psiNat {X y : ℕ} (hX : 1 ≤ X) : 1 ≤ psiNat X y := by
  rw [psiNat_eq_one_add_sum_largestPrime hX]
  omega

/-- A one-term bad number is exactly a square of a prime times a positive
number all of whose prime factors are no larger than that prime. -/
theorem mem_badOneTermSet_iff_exists_prime_sq_mul_smooth {n : ℕ} :
    n ∈ badOneTermSet ↔
      ∃ p m : ℕ, p.Prime ∧ IsSmooth m p ∧ n = p ^ 2 * m := by
  constructor
  · rintro ⟨hnpos, hbad⟩
    have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    rcases hbad with ⟨_, hbad⟩
    rw [consecutiveProduct_one, hpred] at hbad
    rcases hbad with ⟨p, hlargest, hpSq⟩
    obtain ⟨m, hm⟩ := hpSq
    have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
    have hm0 : m ≠ 0 := by
      intro hmzero
      subst m
      simp at hm
      exact hn0 hm
    have hsmooth : IsSmooth m p := by
      rw [isSmooth_iff]
      refine ⟨hm0, ?_⟩
      intro q hqprime hqdiv
      have hqdivn : q ∣ n := by
        rw [hm]
        exact dvd_mul_of_dvd_right hqdiv (p ^ 2)
      exact (largestPrimeFactor_eq_some_iff.mp hlargest).2 q
        (hqprime.mem_primeFactors hqdivn hn0)
    exact ⟨p, m, Nat.prime_of_mem_primeFactors
      (largestPrimeFactor_eq_some_iff.mp hlargest).1, hsmooth, hm⟩
  · rintro ⟨p, m, hp, hsmooth, rfl⟩
    have hm0 : m ≠ 0 := (isSmooth_iff.mp hsmooth).1
    have hp0 : p ≠ 0 := hp.ne_zero
    have hprod0 : p ^ 2 * m ≠ 0 := mul_ne_zero (pow_ne_zero 2 hp0) hm0
    have hprodpos : 1 ≤ p ^ 2 * m := Nat.one_le_iff_ne_zero.mpr hprod0
    refine ⟨hprodpos, ?_⟩
    have hpred : p ^ 2 * m - 1 + 1 = p ^ 2 * m :=
      Nat.sub_add_cancel hprodpos
    rw [IsBadInterval]
    refine ⟨by simp, p, ?_, ?_⟩
    · rw [consecutiveProduct_one, hpred]
      rw [largestPrimeFactor_eq_some_iff]
      constructor
      · exact hp.mem_primeFactors
          (by
            rw [pow_two, mul_assoc]
            exact dvd_mul_right p (p * m)) hprod0
      · intro q hqmem
        have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
        have hqdiv : q ∣ p ^ 2 * m := Nat.dvd_of_mem_primeFactors hqmem
        rcases hqprime.dvd_mul.mp hqdiv with hqpow | hqm
        · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp
            (hqprime.dvd_of_dvd_pow hqpow)
          exact hqp.le
        · exact (isSmooth_iff.mp hsmooth).2 q hqprime hqm
    · rw [consecutiveProduct_one, hpred]
      exact dvd_mul_right (p ^ 2) m

/-- The prime in the source's `n = p²m`, `m` `p`-smooth representation is
unique. This is the disjointness fact needed before converting the exact
one-term count to a sum over primes. -/
theorem prime_unique_of_sq_mul_smooth {n p q m k : ℕ}
    (hp : p.Prime) (hm : IsSmooth m p) (hnp : n = p ^ 2 * m)
    (hq : q.Prime) (hk : IsSmooth k q) (hnq : n = q ^ 2 * k) : p = q := by
  have hnpos : 1 ≤ n := by
    rw [hnp]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero 2 hp.ne_zero) (isSmooth_iff.mp hm).1)
  have hpbad : n ∈ badOneTermSet :=
    mem_badOneTermSet_iff_exists_prime_sq_mul_smooth.mpr
      ⟨p, m, hp, hm, hnp⟩
  have hqbad : n ∈ badOneTermSet :=
    mem_badOneTermSet_iff_exists_prime_sq_mul_smooth.mpr
      ⟨q, k, hq, hk, hnq⟩
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
  rcases hpbad with ⟨_, hpinterval⟩
  rcases hqbad with ⟨_, hqinterval⟩
  rcases hpinterval with ⟨_, hpinterval⟩
  rcases hqinterval with ⟨_, hqinterval⟩
  rw [consecutiveProduct_one, hpred] at hpinterval hqinterval
  rcases hpinterval with ⟨p', hp', _⟩
  rcases hqinterval with ⟨q', hq', _⟩
  have hpp' : p = p' := by
    apply Option.some_injective
    rw [← hp', largestPrimeFactor_eq_some_iff.mpr]
    constructor
    · exact hp.mem_primeFactors
        (hnp ▸ (by
          rw [pow_two, mul_assoc]
          exact dvd_mul_right p (p * m)))
        (Nat.ne_of_gt hnpos)
    · intro r hr
      have hrprime := Nat.prime_of_mem_primeFactors hr
      have hrdiv := Nat.dvd_of_mem_primeFactors hr
      rw [hnp] at hrdiv
      rcases hrprime.dvd_mul.mp hrdiv with hrpow | hrm
      · have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hrprime hp).mp
          (hrprime.dvd_of_dvd_pow hrpow)
        exact hrp.le
      · exact (isSmooth_iff.mp hm).2 r hrprime hrm
  have hqq' : q = q' := by
    apply Option.some_injective
    rw [← hq', largestPrimeFactor_eq_some_iff.mpr]
    constructor
    · exact hq.mem_primeFactors
        (hnq ▸ (by
          rw [pow_two, mul_assoc]
          exact dvd_mul_right q (q * k)))
        (Nat.ne_of_gt hnpos)
    · intro r hr
      have hrprime := Nat.prime_of_mem_primeFactors hr
      have hrdiv := Nat.dvd_of_mem_primeFactors hr
      rw [hnq] at hrdiv
      rcases hrprime.dvd_mul.mp hrdiv with hrpow | hrk
      · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hrprime hq).mp
          (hrprime.dvd_of_dvd_pow hrpow)
        exact hrq.le
      · exact (isSmooth_iff.mp hk).2 r hrprime hrk
  calc
    p = p' := hpp'
    _ = q' := Option.some.inj (hp'.symm.trans hq')
    _ = q := hqq'.symm

/-- The disjoint finite family of representations contributing to Tao's
one-term bad-set identity. The sigma type keeps the prime and its smooth
cofactor separate until injectivity has been proved. -/
noncomputable def badOneTermRepresentations (x : ℕ) :
    Finset (Σ _p : ℕ, ℕ) := by
  classical
  exact ((Finset.Icc 2 x.sqrt).filter Nat.Prime).sigma fun p =>
    Nat.smoothNumbersUpTo (x / p ^ 2) (p + 1)

/-- The natural represented by a prime/smooth-cofactor pair. -/
def badOneTermRepresentationValue (r : Σ _p : ℕ, ℕ) : ℕ :=
  r.1 ^ 2 * r.2

/-- The literal finite intersection `B¹ ∩ [1,x]`. -/
noncomputable def badOneTermNumbersUpTo (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n => n ∈ badOneTermSet

theorem mem_badOneTermRepresentations_iff {x : ℕ} {r : Σ _p : ℕ, ℕ} :
    r ∈ badOneTermRepresentations x ↔
      r.1.Prime ∧ 2 ≤ r.1 ∧ r.1 ≤ x.sqrt ∧
        r.2 ≤ x / r.1 ^ 2 ∧ IsSmooth r.2 r.1 := by
  classical
  simp [badOneTermRepresentations, mem_smoothNumbersUpTo_source,
    and_left_comm, and_assoc]

/-- Forgetting the unique representation produces exactly the finite set
`B¹ ∩ [1,x]`. -/
theorem image_badOneTermRepresentations (x : ℕ) :
    (badOneTermRepresentations x).image badOneTermRepresentationValue =
      badOneTermNumbersUpTo x := by
  classical
  ext n
  rw [badOneTermNumbersUpTo]
  constructor
  · intro hn
    rw [Finset.mem_image] at hn
    rcases hn with ⟨r, hr, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hr' := mem_badOneTermRepresentations_iff.mp hr
    have hm0 : r.2 ≠ 0 := (isSmooth_iff.mp hr'.2.2.2.2).1
    have hp0 : r.1 ≠ 0 := hr'.1.ne_zero
    have hpos : 1 ≤ r.1 ^ 2 * r.2 :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero 2 hp0) hm0)
    have hsquarePos : 0 < r.1 ^ 2 := pow_pos hr'.1.pos 2
    have hle : r.1 ^ 2 * r.2 ≤ x := by
      have := (Nat.le_div_iff_mul_le hsquarePos).mp hr'.2.2.2.1
      simpa only [mul_comm] using this
    exact ⟨⟨hpos, hle⟩,
      mem_badOneTermSet_iff_exists_prime_sq_mul_smooth.mpr
        ⟨r.1, r.2, hr'.1, hr'.2.2.2.2, rfl⟩⟩
  · intro hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨hnpos, hnle⟩, hbad⟩
    rcases mem_badOneTermSet_iff_exists_prime_sq_mul_smooth.mp hbad with
      ⟨p, m, hp, hm, hnmul⟩
    have hmpos : 1 ≤ m :=
      Nat.one_le_iff_ne_zero.mpr (isSmooth_iff.mp hm).1
    have hsqle : p ^ 2 ≤ n := by
      rw [hnmul]
      exact Nat.le_mul_of_pos_right (p ^ 2) hmpos
    have hpsqrt : p ≤ x.sqrt :=
      Nat.le_sqrt'.mpr (hsqle.trans hnle)
    have hpmle : m ≤ x / p ^ 2 := by
      rw [Nat.le_div_iff_mul_le (pow_pos hp.pos 2)]
      have hmulLe : p ^ 2 * m ≤ x := hnmul ▸ hnle
      simpa only [mul_comm] using hmulLe
    rw [Finset.mem_image]
    refine ⟨⟨p, m⟩, ?_, hnmul.symm⟩
    exact mem_badOneTermRepresentations_iff.mpr
      ⟨hp, hp.two_le, hpsqrt, hpmle, hm⟩

/-- The representation-value map is injective on the source-relevant finite
family. Its prime coordinate is forced by the largest-prime-factor condition,
then cancellation forces the smooth cofactor. -/
theorem injOn_badOneTermRepresentationValue (x : ℕ) :
    Set.InjOn badOneTermRepresentationValue (badOneTermRepresentations x) := by
  rintro ⟨p, m⟩ hpm ⟨q, k⟩ hqk heq
  have hpm' := mem_badOneTermRepresentations_iff.mp hpm
  have hqk' := mem_badOneTermRepresentations_iff.mp hqk
  have hpq : p = q := prime_unique_of_sq_mul_smooth
    hpm'.1 hpm'.2.2.2.2 rfl hqk'.1 hqk'.2.2.2.2 heq
  subst q
  have hmk : m = k :=
    Nat.eq_of_mul_eq_mul_left (pow_pos hpm'.1.pos 2) heq
  subst k
  rfl

/-- Cardinality of the representation family, before forgetting the unique
prime/cofactor decomposition. -/
theorem card_badOneTermRepresentations (x : ℕ) :
    (badOneTermRepresentations x).card =
      ∑ p ∈ (Finset.Icc 2 x.sqrt).filter Nat.Prime, psiNat (x / p ^ 2) p := by
  classical
  rw [badOneTermRepresentations, Finset.card_sigma]
  rfl

/-- Tao's exact identity
`#(B¹ ∩ [1,x]) = ∑_{p≤√x} Ψ(x/p²,p)`, with natural division making the
integer endpoints explicit and the sum restricted to primes. -/
theorem badOneTermCount_eq_sum_psiNat (x : ℕ) :
    badOneTermCount x =
      ∑ p ∈ (Finset.Icc 2 x.sqrt).filter Nat.Prime, psiNat (x / p ^ 2) p := by
  classical
  change (badOneTermNumbersUpTo x).card = _
  rw [← image_badOneTermRepresentations x,
    Finset.card_image_iff.mpr (injOn_badOneTermRepresentationValue x),
    card_badOneTermRepresentations]

end Tao2026

import Mathlib.Data.Finsupp.Fin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Max

/-!
# Arithmetic anatomy of a natural number

This file fixes the elementary number-theoretic conventions from Tao,
*Products of consecutive integers with unusual anatomy*, Definition 1.2.
In particular, `largestPrimeFactor` is option-valued so that `0` and `1` do
not acquire fictitious largest prime factors.
-/

namespace Tao2026

/-- The largest prime factor of `n`, and `none` when `n` has no prime factor. -/
def largestPrimeFactor (n : ℕ) : Option ℕ :=
  if h : n.primeFactors.Nonempty then some (n.primeFactors.max' h) else none

@[simp]
theorem largestPrimeFactor_eq_none_iff {n : ℕ} :
    largestPrimeFactor n = none ↔ n = 0 ∨ n = 1 := by
  simp [largestPrimeFactor, Nat.nonempty_primeFactors,
    Nat.le_one_iff_eq_zero_or_eq_one]

theorem largestPrimeFactor_eq_some_iff {n p : ℕ} :
    largestPrimeFactor n = some p ↔
      p ∈ n.primeFactors ∧ ∀ q ∈ n.primeFactors, q ≤ p := by
  simp only [largestPrimeFactor]
  split_ifs with h
  · rw [Option.some_inj]
    exact Finset.max'_eq_iff n.primeFactors h p
  · constructor
    · intro hnone
      cases hnone
    · intro hp
      exact (h ⟨p, hp.1⟩).elim

/-- A natural number is powerful (squarefull) when every prime divisor occurs
with exponent at least two. This deliberately makes `1` powerful and `0`
powerful, matching the literal divisibility predicate; later interval theorems
carry their own positivity hypotheses. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- The squarefree component `s(n)`: the product of prime factors occurring
to odd exponent. For positive `n`, this is the largest natural number of the
form `n / m^2` which is squarefree. -/
def squarefreeComponent (n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support.filter (fun p => Odd (n.factorization p)), p

@[simp]
theorem squarefreeComponent_zero : squarefreeComponent 0 = 1 := by
  simp [squarefreeComponent]

@[simp]
theorem squarefreeComponent_one : squarefreeComponent 1 = 1 := by
  simp [squarefreeComponent]

private theorem squarefree_finsetProduct_of_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (s.prod id) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert p s hp ih =>
      have hprime : p.Prime := hs p (by simp)
      have hsprime : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      have hcoprime : p.Coprime (s.prod id) := by
        rw [hprime.coprime_iff_not_dvd]
        intro hpdvd
        obtain ⟨q, hq, hpq⟩ := (hprime.prime.dvd_finsetProd_iff id).mp hpdvd
        have hqp : q = p := ((hsprime q hq).dvd_iff_eq hprime.ne_one).mp hpq
        exact hp (hqp ▸ hq)
      rw [Finset.prod_insert hp]
      simpa only [id_eq] using
        (Nat.squarefree_mul hcoprime).mpr ⟨hprime.squarefree, ih hsprime⟩

/-- The factorization-parity definition always produces a squarefree number. -/
theorem squarefree_squarefreeComponent (n : ℕ) : Squarefree (squarefreeComponent n) := by
  apply squarefree_finsetProduct_of_primes
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)

/-- The squarefree component uses only prime factors of the original number. -/
theorem squarefreeComponent_dvd (n : ℕ) : squarefreeComponent n ∣ n := by
  apply dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
  simpa [squarefreeComponent] using Nat.prod_primeFactors_dvd n

/-- Prime support of the squarefree component is exactly the odd-valuation
support of `n`. -/
theorem mem_primeFactors_squarefreeComponent_iff {n p : ℕ} :
    p ∈ (squarefreeComponent n).primeFactors ↔
      p ∈ n.primeFactors ∧ Odd (n.factorization p) := by
  have hprime : ∀ q ∈ n.factorization.support.filter
      (fun q => Odd (n.factorization q)), q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)
  rw [squarefreeComponent, Nat.primeFactors_prod hprime]
  simp

/-- Valuation form of powerfulness for nonzero naturals. -/
theorem powerful_iff_factorization_two_le {n : ℕ} (hn : n ≠ 0) :
    Powerful n ↔ ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p := by
  constructor
  · intro h p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact (hprime.pow_dvd_iff_le_factorization hn).mp
      (h p hprime (Nat.dvd_of_mem_primeFactors hp))
  · intro h p hprime hpdvd
    exact (hprime.pow_dvd_iff_le_factorization hn).mpr
      (h p (hprime.mem_primeFactors hpdvd hn))

/-- Tao's squarefree component is obtained by dividing `n` by an actual
perfect square. -/
theorem exists_sq_mul_squarefreeComponent {n : ℕ} (hn : 0 < n) :
    ∃ m : ℕ, m ^ 2 * squarefreeComponent n = n := by
  obtain ⟨a, b, ha, hb, hba, hasquarefree⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hcomponent : a = squarefreeComponent n := by
    have hprimeFactors : a.primeFactors = (squarefreeComponent n).primeFactors := by
      ext p
      rw [mem_primeFactors_squarefreeComponent_iff]
      have hmemA : p ∈ a.primeFactors ↔ a.factorization p ≠ 0 := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      have hmemN : p ∈ n.primeFactors ↔ n.factorization p ≠ 0 := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      have hafac : a.factorization p ≤ 1 :=
        (Nat.squarefree_iff_factorization_le_one ha.ne').mp hasquarefree p
      have hnfac : n.factorization p =
          2 * b.factorization p + a.factorization p := by
        rw [← hba, Nat.factorization_mul (pow_ne_zero 2 hb.ne') ha.ne',
          Nat.factorization_pow]
        simp
      have hparity : Odd (n.factorization p) ↔ a.factorization p = 1 := by
        rw [Nat.odd_iff, hnfac]
        omega
      constructor
      · intro hp
        have hapos : a.factorization p = 1 := by
          have := hmemA.mp hp
          omega
        refine ⟨hmemN.mpr ?_, hparity.mpr hapos⟩
        rw [hnfac, hapos]
        omega
      · rintro ⟨_, hpodd⟩
        exact hmemA.mpr (by rw [hparity.mp hpodd]; omega)
    calc
      a = ∏ p ∈ a.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hasquarefree).symm
      _ = ∏ p ∈ (squarefreeComponent n).primeFactors, p := by
        rw [hprimeFactors]
      _ = squarefreeComponent n :=
        Nat.prod_primeFactors_of_squarefree (squarefree_squarefreeComponent n)
  exact ⟨b, hcomponent ▸ hba⟩

/-- Uniqueness of the squarefree factor after removing a square. This is the
source footnote's characterization of `s(n)`. -/
theorem eq_squarefreeComponent_of_sq_mul {n a m : ℕ} (hn : 0 < n)
    (ha : Squarefree a) (ham : m ^ 2 * a = n) : a = squarefreeComponent n := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ham
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at ham
    omega
  have hprimeFactors : a.primeFactors = (squarefreeComponent n).primeFactors := by
    ext p
    rw [mem_primeFactors_squarefreeComponent_iff]
    have hmemA : p ∈ a.primeFactors ↔ a.factorization p ≠ 0 := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    have hmemN : p ∈ n.primeFactors ↔ n.factorization p ≠ 0 := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    have hafac : a.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one ha0).mp ha p
    have hnfac : n.factorization p =
        2 * m.factorization p + a.factorization p := by
      rw [← ham, Nat.factorization_mul (pow_ne_zero 2 hm0) ha0,
        Nat.factorization_pow]
      simp
    have hparity : Odd (n.factorization p) ↔ a.factorization p = 1 := by
      rw [Nat.odd_iff, hnfac]
      omega
    constructor
    · intro hp
      have hapos : a.factorization p = 1 := by
        have := hmemA.mp hp
        omega
      refine ⟨hmemN.mpr ?_, hparity.mpr hapos⟩
      rw [hnfac, hapos]
      omega
    · rintro ⟨_, hpodd⟩
      exact hmemA.mpr (by rw [hparity.mp hpodd]; omega)
  calc
    a = ∏ p ∈ a.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree ha).symm
    _ = ∏ p ∈ (squarefreeComponent n).primeFactors, p := by
      rw [hprimeFactors]
    _ = squarefreeComponent n :=
      Nat.prod_primeFactors_of_squarefree (squarefree_squarefreeComponent n)

/-- Two positive naturals have the same squarefree component exactly when
their product is a square. -/
theorem squarefreeComponent_eq_iff_mul_eq_sq {a b : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    squarefreeComponent a = squarefreeComponent b ↔
      ∃ m : ℕ, a * b = m ^ 2 := by
  constructor
  · intro hcomponents
    obtain ⟨u, hu⟩ := exists_sq_mul_squarefreeComponent ha.bot_lt
    obtain ⟨v, hv⟩ := exists_sq_mul_squarefreeComponent hb.bot_lt
    refine ⟨u * v * squarefreeComponent a, ?_⟩
    rw [← hu, ← hv, ← hcomponents]
    ring
  · rintro ⟨m, hm⟩
    have hm0 : m ≠ 0 := by
      intro hmzero
      subst m
      simp at hm
      exact (mul_ne_zero ha hb) hm
    have hparity (p : ℕ) :
        Odd (a.factorization p) ↔ Odd (b.factorization p) := by
      have hfactorization :
          a.factorization p + b.factorization p = 2 * m.factorization p := by
        rw [← Nat.factorization_mul ha hb, hm, Nat.factorization_pow]
        simp
      rw [Nat.odd_iff, Nat.odd_iff]
      omega
    have hprimeFactors :
        (squarefreeComponent a).primeFactors =
          (squarefreeComponent b).primeFactors := by
      ext p
      rw [mem_primeFactors_squarefreeComponent_iff,
        mem_primeFactors_squarefreeComponent_iff]
      constructor
      · rintro ⟨_, hpOdd⟩
        have hpOddB := (hparity p).mp hpOdd
        have hpFacB : b.factorization p ≠ 0 := by
          intro hpzero
          rw [hpzero] at hpOddB
          exact Nat.not_odd_zero hpOddB
        exact ⟨by
          rw [← Nat.support_factorization, Finsupp.mem_support_iff]
          exact hpFacB, hpOddB⟩
      · rintro ⟨_, hpOdd⟩
        have hpOddA := (hparity p).mpr hpOdd
        have hpFacA : a.factorization p ≠ 0 := by
          intro hpzero
          rw [hpzero] at hpOddA
          exact Nat.not_odd_zero hpOddA
        exact ⟨by
          rw [← Nat.support_factorization, Finsupp.mem_support_iff]
          exact hpFacA, hpOddA⟩
    calc
      squarefreeComponent a =
          ∏ p ∈ (squarefreeComponent a).primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree
          (squarefree_squarefreeComponent a)).symm
      _ = ∏ p ∈ (squarefreeComponent b).primeFactors, p := by
        rw [hprimeFactors]
      _ = squarefreeComponent b :=
        Nat.prod_primeFactors_of_squarefree
          (squarefree_squarefreeComponent b)

/-- Every positive powerful number has Tao's square-times-cube form
`a² b³`, with a positive squarefree cube base. Conversely every such form is
powerful. This is the decomposition used in the reduction to Corollary 2.11. -/
theorem powerful_iff_exists_sq_mul_cube_squarefree {n : ℕ} (hn : 0 < n) :
    Powerful n ↔
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree b ∧ n = a ^ 2 * b ^ 3 := by
  constructor
  · intro hpowerful
    obtain ⟨m, hm⟩ := exists_sq_mul_squarefreeComponent hn
    let b := squarefreeComponent n
    have hbSquarefree : Squarefree b := squarefree_squarefreeComponent n
    have hb0 : b ≠ 0 := by
      intro hbzero
      rw [show squarefreeComponent n = 0 from hbzero] at hm
      simp at hm
      exact hn.ne' hm.symm
    have hm0 : m ≠ 0 := by
      intro hmzero
      subst m
      simp at hm
      exact hn.ne' hm.symm
    have hbDvdM : b ∣ m := by
      rw [← Nat.factorization_prime_le_iff_dvd hb0 hm0]
      intro p hp
      by_cases hpdivb : p ∣ b
      · have hbFac : b.factorization p = 1 :=
          Nat.factorization_eq_one_of_squarefree hbSquarefree hp hpdivb
        have hpdivn : p ∣ n :=
          dvd_trans hpdivb (squarefreeComponent_dvd n)
        have hpSqDivN : p ^ 2 ∣ n := hpowerful p hp hpdivn
        have hnFac : 2 ≤ n.factorization p :=
          (hp.pow_dvd_iff_le_factorization hn.ne').mp hpSqDivN
        have hfactorization : n.factorization p =
            2 * m.factorization p + b.factorization p := by
          rw [← hm, Nat.factorization_mul (pow_ne_zero 2 hm0) hb0,
            Nat.factorization_pow]
          simp
        omega
      · have hbFac : b.factorization p = 0 := by
          have hnotOne : ¬1 ≤ b.factorization p := by
            rwa [← hp.dvd_iff_one_le_factorization hb0]
          omega
        rw [hbFac]
        exact Nat.zero_le _
    obtain ⟨a, ha⟩ := hbDvdM
    refine ⟨a, b, ?_, hb0.bot_lt, hbSquarefree, ?_⟩
    · apply Nat.pos_of_ne_zero
      intro hazero
      subst a
      simp at ha
      exact hm0 ha
    · rw [← hm, ha]
      ring
  · rintro ⟨a, b, ha, hb, _, rfl⟩
    intro p hp hpdiv
    rcases hp.dvd_mul.mp hpdiv with hpdiva | hpdivb
    · have hpa : p ∣ a := hp.dvd_of_dvd_pow hpdiva
      exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hpa 2) (b ^ 3)
    · have hpb : p ∣ b := hp.dvd_of_dvd_pow hpdivb
      have hpSqDivCube : p ^ 2 ∣ b ^ 3 := by
        exact pow_dvd_pow_of_dvd_of_le hpb (by omega)
      exact dvd_mul_of_dvd_right hpSqDivCube (a ^ 2)

/-- Uniqueness of the positive square-times-squarefree-cube parameters. -/
theorem sq_mul_cube_squarefree_unique {n a b c d : ℕ} (hn : 0 < n)
    (hb : 0 < b) (hbSquarefree : Squarefree b)
    (hdSquarefree : Squarefree d)
    (hab : n = a ^ 2 * b ^ 3) (hcd : n = c ^ 2 * d ^ 3) :
    a = c ∧ b = d := by
  have hbComponent : b = squarefreeComponent n :=
    eq_squarefreeComponent_of_sq_mul hn hbSquarefree (by
      calc
        (a * b) ^ 2 * b = a ^ 2 * b ^ 3 := by ring
        _ = n := hab.symm)
  have hdComponent : d = squarefreeComponent n :=
    eq_squarefreeComponent_of_sq_mul hn hdSquarefree (by
      calc
        (c * d) ^ 2 * d = c ^ 2 * d ^ 3 := by ring
        _ = n := hcd.symm)
  have hbd : b = d := hbComponent.trans hdComponent.symm
  have hcd' : n = c ^ 2 * b ^ 3 := by
    simpa only [hbd] using hcd
  have hsquares : a ^ 2 = c ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hb 3)
    exact hab.symm.trans hcd'
  exact ⟨Nat.pow_left_injective (by decide : 2 ≠ 0) hsquares, hbd⟩

end Tao2026

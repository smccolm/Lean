import Tao2026.SmoothNumberCriticalLower
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Finite Canfield--Erdős--Pomerance prime packets

This file begins the primary-source proof of the critical smooth-number lower
bound.  It formalizes the unordered repeated-prime packet and the exact
multinomial inequality underlying Canfield--Erdős--Pomerance (3.11).
-/

open scoped BigOperators

namespace Tao2026

noncomputable section

open Finset

/-- The number of distinct permutations of a multiset never exceeds the
factorial of its cardinality. -/
theorem multiset_countPerms_le_factorial {α : Type*} [DecidableEq α]
    (m : Multiset α) : m.countPerms ≤ Nat.factorial m.card := by
  rw [Multiset.countPerms, Finsupp.multinomial, Multiset.toFinsupp_sum_eq]
  exact Nat.div_le_self _ _

/-- Multinomial expansion with every unordered coefficient bounded by `r!`.
This is the abstract finite inequality behind CEP (3.11). -/
theorem sum_pow_le_factorial_mul_sum_sym
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (r : ℕ) :
    (∑ p ∈ P, w p) ^ r ≤
      (Nat.factorial r : ℝ) * ∑ s ∈ P.sym r, (s.val.map w).prod := by
  rw [Finset.sum_pow]
  calc
    ∑ s ∈ P.sym r, (s.val.countPerms : ℝ) * (s.val.map w).prod ≤
        ∑ s ∈ P.sym r, (Nat.factorial r : ℝ) * (s.val.map w).prod := by
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_right
      · have hcount := multiset_countPerms_le_factorial s.val
        rw [s.property] at hcount
        exact_mod_cast hcount
      · exact Multiset.prod_nonneg (by
          intro z hz
          rw [Multiset.mem_map] at hz
          obtain ⟨p, hp, rfl⟩ := hz
          exact hw p (Finset.mem_sym_iff.mp hs p hp))
    _ = (Nat.factorial r : ℝ) * ∑ s ∈ P.sym r, (s.val.map w).prod := by
      rw [Finset.mul_sum]

/-- Division form of the unordered multinomial packet bound. -/
theorem pow_div_factorial_le_sum_sym
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (r : ℕ) :
    (∑ p ∈ P, w p) ^ r / (Nat.factorial r : ℝ) ≤
      ∑ s ∈ P.sym r, (s.val.map w).prod := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Nat.factorial r)]
  simpa [mul_comm] using sum_pow_le_factorial_mul_sum_sym P w hw r

/-- The CEP packet of unordered, repetition-permitted selections of exactly
`r` primes from a bounded-prime finset. -/
def cepPrimePacket {y : ℕ} (P : Finset (TaoBoundedPrime y)) (r : ℕ) :
    Finset (Sym (TaoBoundedPrime y) r) :=
  P.sym r

/-- The reciprocal weight of one unordered repeated-prime packet element. -/
def cepPrimePacketWeight {y r : ℕ} (s : Sym (TaoBoundedPrime y) r) : ℝ :=
  (s.val.map fun p => ((p : ℕ) : ℝ)⁻¹).prod

/-- A packet's multiplicative reciprocal weight is exactly the reciprocal of
the integer represented by its prime multiset. -/
theorem cepPrimePacketWeight_eq_inv_smoothExponentValue {y r : ℕ}
    (s : Sym (TaoBoundedPrime y) r) :
    cepPrimePacketWeight s = ((smoothExponentValue s : ℕ) : ℝ)⁻¹ := by
  rw [cepPrimePacketWeight, smoothExponentValue_eq_multisetProd]
  simp

/-- The distinct integer products represented by one CEP prime packet. -/
noncomputable def cepPrimePacketProducts {y : ℕ}
    (P : Finset (TaoBoundedPrime y)) (r : ℕ) : Finset ℕ :=
  (cepPrimePacket P r).image smoothExponentValue

/-- Unique factorization removes all overcounting when the symmetric packet
is evaluated as a finite set of integers. -/
theorem sum_inv_cepPrimePacketProducts_eq_packetWeightSum
    {y : ℕ} (P : Finset (TaoBoundedPrime y)) (r : ℕ) :
    ∑ n ∈ cepPrimePacketProducts P r, ((n : ℝ)⁻¹) =
      ∑ s ∈ cepPrimePacket P r, cepPrimePacketWeight s := by
  rw [cepPrimePacketProducts, Finset.sum_image]
  · simp_rw [cepPrimePacketWeight_eq_inv_smoothExponentValue]
  · exact smoothExponentValue_injective_fixed.injOn

theorem mem_cepPrimePacketProducts_isSmooth {y r n : ℕ}
    {P : Finset (TaoBoundedPrime y)}
    (hn : n ∈ cepPrimePacketProducts P r) : IsSmooth n y := by
  rw [cepPrimePacketProducts, Finset.mem_image] at hn
  obtain ⟨s, hs, rfl⟩ := hn
  exact smoothExponentValue_isSmooth s

theorem mem_cepPrimePacketProducts_le_pow {y r n : ℕ}
    {P : Finset (TaoBoundedPrime y)}
    (hn : n ∈ cepPrimePacketProducts P r) : n ≤ y ^ r := by
  rw [cepPrimePacketProducts, Finset.mem_image] at hn
  obtain ⟨s, hs, rfl⟩ := hn
  exact smoothExponentValue_le_pow s

theorem pow_card_le_multisetMap_prod
    {α : Type*} {L : ℝ} (f : α → ℝ) {s : Multiset α} (hL : 0 ≤ L)
    (hs : ∀ z ∈ s, L ≤ f z) :
    L ^ s.card ≤ (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons n s ih =>
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ']
      have hn : L ≤ f n := hs n (by simp)
      exact mul_le_mul hn
        (ih (by intro m hm; exact hs m (by simp [hm])))
        (pow_nonneg hL _) (hL.trans hn)

theorem multisetMap_prod_le_pow_card
    {α : Type*} {U : ℝ} (f : α → ℝ) {s : Multiset α}
    (hf0 : ∀ z ∈ s, 0 ≤ f z) (hs : ∀ z ∈ s, f z ≤ U) :
    (s.map f).prod ≤ U ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons n s ih =>
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ']
      have hn0 : 0 ≤ f n := hf0 n (by simp)
      have hn : f n ≤ U := hs n (by simp)
      exact mul_le_mul hn
        (ih (by intro m hm; exact hf0 m (by simp [hm]))
          (by intro m hm; exact hs m (by simp [hm])))
        (Multiset.prod_nonneg (by
          intro z hz
          rw [Multiset.mem_map] at hz
          obtain ⟨m, hm, rfl⟩ := hz
          exact hf0 m (by simp [hm])))
        (hn0.trans hn)

/-- A product selected from one packet is at least the corresponding power
of any common lower endpoint for the packet's prime alphabet. -/
theorem pow_le_cast_cepPrimePacketProduct
    {y r n : ℕ} {P : Finset (TaoBoundedPrime y)} {L : ℝ}
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, L ≤ ((p : ℕ) : ℝ))
    (hn : n ∈ cepPrimePacketProducts P r) :
    L ^ r ≤ (n : ℝ) := by
  rw [cepPrimePacketProducts, Finset.mem_image] at hn
  obtain ⟨s, hs, rfl⟩ := hn
  rw [smoothExponentValue_eq_multisetProd, Nat.cast_multiset_prod]
  have hprod := pow_card_le_multisetMap_prod
    (fun p : TaoBoundedPrime y => ((p : ℕ) : ℝ)) (s := s.val) hL (by
      intro p hp
      exact hP p
        ((Finset.mem_sym_iff.mp (by simpa [cepPrimePacket] using hs)) p hp))
  simpa [s.property] using hprod

/-- A product selected from one packet is at most the corresponding power
of any common upper endpoint for the packet's prime alphabet. -/
theorem cast_cepPrimePacketProduct_le_pow
    {y r n : ℕ} {P : Finset (TaoBoundedPrime y)} {U : ℝ}
    (hP : ∀ p ∈ P, ((p : ℕ) : ℝ) ≤ U)
    (hn : n ∈ cepPrimePacketProducts P r) :
    (n : ℝ) ≤ U ^ r := by
  rw [cepPrimePacketProducts, Finset.mem_image] at hn
  obtain ⟨s, hs, rfl⟩ := hn
  rw [smoothExponentValue_eq_multisetProd, Nat.cast_multiset_prod]
  have hprod := multisetMap_prod_le_pow_card
    (fun p : TaoBoundedPrime y => ((p : ℕ) : ℝ)) (s := s.val)
    (by intro p hp; positivity) (by
      intro p hp
      exact hP p
        ((Finset.mem_sym_iff.mp (by simpa [cepPrimePacket] using hs)) p hp))
  simpa [s.property] using hprod

/-- Every prime divisor of a packet product belongs to the packet's prime
alphabet. -/
theorem exists_mem_of_prime_dvd_cepPrimePacketProduct
    {y r n q : ℕ} {P : Finset (TaoBoundedPrime y)}
    (hn : n ∈ cepPrimePacketProducts P r) (hq : q.Prime) (hqn : q ∣ n) :
    ∃ p ∈ P, q = (p : ℕ) := by
  rw [cepPrimePacketProducts, Finset.mem_image] at hn
  obtain ⟨s, hs, rfl⟩ := hn
  rw [smoothExponentValue_eq_multisetProd] at hqn
  obtain ⟨a, ha, hqa⟩ := hq.prime.exists_mem_multiset_dvd hqn
  rw [Multiset.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  have hpP : p ∈ P := by
    apply (Finset.mem_sym_iff.mp (by simpa [cepPrimePacket] using hs)) p hp
  exact ⟨p, hpP,
    (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primesLE p.2)).mp hqa⟩

/-- Exact CEP (3.11) for one finite prime interval, before rewriting packet
weights as reciprocals of their integer products. -/
theorem reciprocalPrimeSum_pow_div_factorial_le_packetWeightSum
    {y : ℕ} (P : Finset (TaoBoundedPrime y)) (r : ℕ) :
    (∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹)) ^ r / (Nat.factorial r : ℝ) ≤
      ∑ s ∈ cepPrimePacket P r, cepPrimePacketWeight s := by
  simpa [cepPrimePacket, cepPrimePacketWeight] using
    pow_div_factorial_le_sum_sym P
      (fun p => (((p : ℕ) : ℝ)⁻¹)) (by intro p hp; positivity) r

/-- CEP (3.11) as a lower bound for the reciprocal sum over distinct integer
products.  The preceding lemmas certify that every target is `y`-smooth and
at most `y^r`. -/
theorem reciprocalPrimeSum_pow_div_factorial_le_productReciprocalSum
    {y : ℕ} (P : Finset (TaoBoundedPrime y)) (r : ℕ) :
    (∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹)) ^ r / (Nat.factorial r : ℝ) ≤
      ∑ n ∈ cepPrimePacketProducts P r, ((n : ℝ)⁻¹) := by
  rw [sum_inv_cepPrimePacketProducts_eq_packetWeightSum]
  exact reciprocalPrimeSum_pow_div_factorial_le_packetWeightSum P r

/-! ## The finite product over CEP prime intervals -/

/-- Choices of one integer product from each prime band in a finite family.
This is the tuple set indexed by `i` in the right side of CEP (3.11). -/
noncomputable def cepMultiscalePacketChoices
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ) :
    Finset (∀ j, j ∈ J → ℕ) :=
  J.pi fun j => cepPrimePacketProducts (P j) (r j)

/-- The integer obtained by multiplying one packet product from every band. -/
def cepMultiscalePacketValue
    {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (f : ∀ j, j ∈ J → ℕ) : ℕ :=
  ∏ j ∈ J.attach, f j.1 j.2

/-- The product of the reciprocal weights selected from every band. -/
def cepMultiscalePacketWeight
    {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (f : ∀ j, j ∈ J → ℕ) : ℝ :=
  ∏ j ∈ J.attach, ((f j.1 j.2 : ℕ) : ℝ)⁻¹

theorem mem_cepMultiscalePacketChoices_iff
    {ι : Type*} [DecidableEq ι] {y : ℕ} {J : Finset ι}
    {P : ι → Finset (TaoBoundedPrime y)} {r : ι → ℕ}
    {f : ∀ j, j ∈ J → ℕ} :
    f ∈ cepMultiscalePacketChoices J P r ↔
      ∀ j (hj : j ∈ J), f j hj ∈ cepPrimePacketProducts (P j) (r j) := by
  simp [cepMultiscalePacketChoices]

/-- Multiplicativity turns the tuple weight into the reciprocal of its
combined integer product. -/
theorem cepMultiscalePacketWeight_eq_inv_value
    {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (f : ∀ j, j ∈ J → ℕ) :
    cepMultiscalePacketWeight J f = ((cepMultiscalePacketValue J f : ℕ) : ℝ)⁻¹ := by
  simp [cepMultiscalePacketWeight, cepMultiscalePacketValue]

theorem isSmooth_multiset_prod_of_isSmooth {y : ℕ} {s : Multiset ℕ}
    (hs : ∀ n ∈ s, IsSmooth n y) : IsSmooth s.prod y := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [isSmooth_iff]
      exact ⟨one_ne_zero, fun p hp hpdvd => (hp.not_dvd_one hpdvd).elim⟩
  | @cons n s ih =>
      rw [Multiset.prod_cons]
      exact Nat.mul_mem_smoothNumbers
        (hs n (by simp))
        (ih (by intro m hm; exact hs m (by simp [hm])))

/-- Every combined tuple produced by the multiscale packet remains smooth at
the common prime cutoff. -/
theorem cepMultiscalePacketValue_isSmooth
    {ι : Type*} [DecidableEq ι] {y : ℕ} {J : Finset ι}
    {P : ι → Finset (TaoBoundedPrime y)} {r : ι → ℕ}
    {f : ∀ j, j ∈ J → ℕ}
    (hf : f ∈ cepMultiscalePacketChoices J P r) :
    IsSmooth (cepMultiscalePacketValue J f) y := by
  change IsSmooth
    ((J.attach.1.map fun j => f j.1 j.2).prod) y
  apply isSmooth_multiset_prod_of_isSmooth
  intro n hn
  rw [Multiset.mem_map] at hn
  obtain ⟨j, hj, rfl⟩ := hn
  exact mem_cepPrimePacketProducts_isSmooth
    ((mem_cepMultiscalePacketChoices_iff.mp hf) j.1 j.2)

/-- The combined tuple is bounded by the product of the bandwise power
budgets, hence by `y` to the total selected multiplicity. -/
theorem cepMultiscalePacketValue_le_pow_sum
    {ι : Type*} [DecidableEq ι] {y : ℕ} {J : Finset ι}
    {P : ι → Finset (TaoBoundedPrime y)} {r : ι → ℕ}
    {f : ∀ j, j ∈ J → ℕ}
    (hf : f ∈ cepMultiscalePacketChoices J P r) :
    cepMultiscalePacketValue J f ≤ y ^ ∑ j ∈ J, r j := by
  calc
    cepMultiscalePacketValue J f =
        ∏ j ∈ J.attach, f j.1 j.2 := rfl
    _ ≤ ∏ j ∈ J.attach, y ^ r j.1 := by
      apply Finset.prod_le_prod'
      intro j hj
      exact mem_cepPrimePacketProducts_le_pow
        ((mem_cepMultiscalePacketChoices_iff.mp hf) j.1 j.2)
    _ = y ^ ∑ j ∈ J.attach, r j.1 := by
      exact Finset.prod_pow_eq_pow_sum J.attach (fun j => r j.1) y
    _ = y ^ ∑ j ∈ J, r j := by
      rw [Finset.sum_attach]

/-- Every combined packet value is at least the product of the bandwise
lower-endpoint powers. -/
theorem prod_pow_le_cast_cepMultiscalePacketValue
    {ι : Type*} [DecidableEq ι] {y : ℕ} {J : Finset ι}
    {P : ι → Finset (TaoBoundedPrime y)} {r : ι → ℕ} {L : ι → ℝ}
    {f : ∀ j, j ∈ J → ℕ}
    (hL : ∀ j ∈ J, 0 ≤ L j)
    (hP : ∀ j (_hj : j ∈ J), ∀ p ∈ P j, L j ≤ ((p : ℕ) : ℝ))
    (hf : f ∈ cepMultiscalePacketChoices J P r) :
    ∏ j ∈ J, L j ^ r j ≤ (cepMultiscalePacketValue J f : ℝ) := by
  have hprod :
      (∏ j ∈ J.attach, L j.1 ^ r j.1) ≤
        ∏ j ∈ J.attach, ((f j.1 j.2 : ℕ) : ℝ) := by
    apply Finset.prod_le_prod
    · intro j hj
      exact pow_nonneg (hL j.1 j.2) _
    · intro j hj
      exact pow_le_cast_cepPrimePacketProduct (hL j.1 j.2)
        (hP j.1 j.2) ((mem_cepMultiscalePacketChoices_iff.mp hf) j.1 j.2)
  calc
    ∏ j ∈ J, L j ^ r j = ∏ j ∈ J.attach, L j.1 ^ r j.1 := by
      exact (Finset.prod_attach J (fun j => L j ^ r j)).symm
    _ ≤ ∏ j ∈ J.attach, ((f j.1 j.2 : ℕ) : ℝ) := hprod
    _ = (cepMultiscalePacketValue J f : ℝ) := by
      simp [cepMultiscalePacketValue]

/-- Upper-endpoint companion to `prod_pow_le_cast_cepMultiscalePacketValue`. -/
theorem cast_cepMultiscalePacketValue_le_prod_pow
    {ι : Type*} [DecidableEq ι] {y : ℕ} {J : Finset ι}
    {P : ι → Finset (TaoBoundedPrime y)} {r : ι → ℕ} {U : ι → ℝ}
    {f : ∀ j, j ∈ J → ℕ}
    (hP : ∀ j (_hj : j ∈ J), ∀ p ∈ P j, ((p : ℕ) : ℝ) ≤ U j)
    (hf : f ∈ cepMultiscalePacketChoices J P r) :
    (cepMultiscalePacketValue J f : ℝ) ≤ ∏ j ∈ J, U j ^ r j := by
  have hprod :
      (∏ j ∈ J.attach, ((f j.1 j.2 : ℕ) : ℝ)) ≤
        ∏ j ∈ J.attach, U j.1 ^ r j.1 := by
    apply Finset.prod_le_prod
    · intro j hj
      positivity
    · intro j hj
      exact cast_cepPrimePacketProduct_le_pow (hP j.1 j.2)
        ((mem_cepMultiscalePacketChoices_iff.mp hf) j.1 j.2)
  calc
    (cepMultiscalePacketValue J f : ℝ) =
        ∏ j ∈ J.attach, ((f j.1 j.2 : ℕ) : ℝ) := by
      simp [cepMultiscalePacketValue]
    _ ≤ ∏ j ∈ J.attach, U j.1 ^ r j.1 := hprod
    _ = ∏ j ∈ J, U j ^ r j :=
      Finset.prod_attach J (fun j => U j ^ r j)

/-- The finite set of combined integer products represented by the
multiscale packet. -/
noncomputable def cepMultiscalePacketProducts
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ) : Finset ℕ :=
  (cepMultiscalePacketChoices J P r).image (cepMultiscalePacketValue J)

/-- Arithmetic separation condition for a family of packet bands: products
selected in distinct bands are coprime, even when taken from two different
tuples. Disjoint prime intervals will discharge this condition. -/
def CepMultiscaleBandsPairwiseCoprime
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ) : Prop :=
  ∀ ⦃f g : ∀ j, j ∈ J → ℕ⦄,
    f ∈ cepMultiscalePacketChoices J P r →
    g ∈ cepMultiscalePacketChoices J P r →
    ∀ j (hj : j ∈ J) k (hk : k ∈ J), j ≠ k →
      Nat.Coprime (f j hj) (g k hk)

/-- Pairwise coprimality lets one recover every coordinate from the combined
integer product. -/
theorem injOn_cepMultiscalePacketValue_of_pairwiseCoprime
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ)
    (hcop : CepMultiscaleBandsPairwiseCoprime J P r) :
    Set.InjOn (cepMultiscalePacketValue J)
      (cepMultiscalePacketChoices J P r) := by
  intro f hf g hg hfg
  apply funext
  intro j
  apply funext
  intro hj
  let fRest : ℕ :=
    ∏ k ∈ J.attach \ {⟨j, hj⟩}, f k.1 k.2
  let gRest : ℕ :=
    ∏ k ∈ J.attach \ {⟨j, hj⟩}, g k.1 k.2
  have hfSplit : cepMultiscalePacketValue J f = f j hj * fRest := by
    simpa [cepMultiscalePacketValue, fRest] using
      (Finset.prod_eq_mul_prod_diff_singleton_of_mem
        (s := J.attach) (i := ⟨j, hj⟩) (f := fun k => f k.1 k.2) (by simp))
  have hgSplit : cepMultiscalePacketValue J g = g j hj * gRest := by
    simpa [cepMultiscalePacketValue, gRest] using
      (Finset.prod_eq_mul_prod_diff_singleton_of_mem
        (s := J.attach) (i := ⟨j, hj⟩) (f := fun k => g k.1 k.2) (by simp))
  have hcopFG : Nat.Coprime (f j hj) gRest := by
    dsimp [gRest]
    rw [Nat.coprime_prod_right_iff]
    intro k hk
    apply hcop hf hg j hj k.1 k.2
    intro hjk
    have hkeq : k = ⟨j, hj⟩ := Subtype.ext hjk.symm
    subst k
    simp at hk
  have hcopGF : Nat.Coprime (g j hj) fRest := by
    dsimp [fRest]
    rw [Nat.coprime_prod_right_iff]
    intro k hk
    apply hcop hg hf j hj k.1 k.2
    intro hjk
    have hkeq : k = ⟨j, hj⟩ := Subtype.ext hjk.symm
    subst k
    simp at hk
  apply Nat.dvd_antisymm
  · apply hcopFG.dvd_of_dvd_mul_right
    rw [← hgSplit, ← hfg, hfSplit]
    exact dvd_mul_right _ _
  · apply hcopGF.dvd_of_dvd_mul_right
    rw [← hfSplit, hfg, hgSplit]
    exact dvd_mul_right _ _

/-- Products drawn from disjoint prime alphabets are pairwise coprime across
bands. This is the unique-factorization separation used in CEP (3.11). -/
theorem cepMultiscaleBandsPairwiseCoprime_of_disjoint
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ)
    (hdisj : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (P j) (P k)) :
    CepMultiscaleBandsPairwiseCoprime J P r := by
  intro f g hf hg j hj k hk hjk
  apply Nat.coprime_of_dvd
  intro q hq hqf hqg
  have hfj : f j hj ∈ cepPrimePacketProducts (P j) (r j) :=
    (mem_cepMultiscalePacketChoices_iff.mp hf) j hj
  have hgk : g k hk ∈ cepPrimePacketProducts (P k) (r k) :=
    (mem_cepMultiscalePacketChoices_iff.mp hg) k hk
  obtain ⟨p, hpP, hqp⟩ :=
    exists_mem_of_prime_dvd_cepPrimePacketProduct hfj hq hqf
  obtain ⟨p', hp'P, hqp'⟩ :=
    exists_mem_of_prime_dvd_cepPrimePacketProduct hgk hq hqg
  have hpp' : p = p' := by
    apply Subtype.ext
    exact hqp.symm.trans hqp'
  subst p'
  exact (Finset.disjoint_left.mp (hdisj j hj k hk hjk)) hpP hp'P

/-- Disjoint prime bands make the combined product map injective. -/
theorem injOn_cepMultiscalePacketValue_of_disjoint
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ)
    (hdisj : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (P j) (P k)) :
    Set.InjOn (cepMultiscalePacketValue J)
      (cepMultiscalePacketChoices J P r) :=
  injOn_cepMultiscalePacketValue_of_pairwiseCoprime J P r
    (cepMultiscaleBandsPairwiseCoprime_of_disjoint J P r hdisj)

theorem mem_cepMultiscalePacketProducts_isSmooth
    {ι : Type*} [DecidableEq ι] {y n : ℕ} {J : Finset ι}
    {P : ι → Finset (TaoBoundedPrime y)} {r : ι → ℕ}
    (hn : n ∈ cepMultiscalePacketProducts J P r) : IsSmooth n y := by
  rw [cepMultiscalePacketProducts, Finset.mem_image] at hn
  obtain ⟨f, hf, rfl⟩ := hn
  exact cepMultiscalePacketValue_isSmooth hf

theorem mem_cepMultiscalePacketProducts_le_pow_sum
    {ι : Type*} [DecidableEq ι] {y n : ℕ} {J : Finset ι}
    {P : ι → Finset (TaoBoundedPrime y)} {r : ι → ℕ}
    (hn : n ∈ cepMultiscalePacketProducts J P r) :
    n ≤ y ^ ∑ j ∈ J, r j := by
  rw [cepMultiscalePacketProducts, Finset.mem_image] at hn
  obtain ⟨f, hf, rfl⟩ := hn
  exact cepMultiscalePacketValue_le_pow_sum hf

/-- Once the source's disjoint-band arithmetic supplies injectivity, the
tuple reciprocal sum is literally a sum over distinct combined integers. -/
theorem sum_inv_cepMultiscalePacketProducts_eq_weightSum_of_injOn
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ)
    (hinj : Set.InjOn (cepMultiscalePacketValue J)
      (cepMultiscalePacketChoices J P r)) :
    ∑ n ∈ cepMultiscalePacketProducts J P r, ((n : ℝ)⁻¹) =
      ∑ f ∈ cepMultiscalePacketChoices J P r, cepMultiscalePacketWeight J f := by
  rw [cepMultiscalePacketProducts, Finset.sum_image hinj]
  simp_rw [cepMultiscalePacketWeight_eq_inv_value]

/-- Exact finite distributive expansion of the product of packet reciprocal
sums.  This is the product-to-tuple transition in CEP (3.11). -/
theorem prod_productReciprocalSum_eq_multiscalePacketWeightSum
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ) :
    ∏ j ∈ J, (∑ n ∈ cepPrimePacketProducts (P j) (r j), ((n : ℝ)⁻¹)) =
      ∑ f ∈ cepMultiscalePacketChoices J P r, cepMultiscalePacketWeight J f := by
  simpa [cepMultiscalePacketChoices, cepMultiscalePacketWeight] using
    (Finset.prod_sum J (fun j => cepPrimePacketProducts (P j) (r j))
      (fun _j n => ((n : ℝ)⁻¹)))

/-- The full finite product form of CEP (3.11), retaining the prime bands and
their multiplicities as explicit data. -/
theorem prod_reciprocalPrimeSum_pow_div_factorial_le_multiscalePacketWeightSum
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ) :
    ∏ j ∈ J,
        (∑ p ∈ P j, (((p : ℕ) : ℝ)⁻¹)) ^ r j /
          (Nat.factorial (r j) : ℝ) ≤
      ∑ f ∈ cepMultiscalePacketChoices J P r, cepMultiscalePacketWeight J f := by
  calc
    ∏ j ∈ J,
        (∑ p ∈ P j, (((p : ℕ) : ℝ)⁻¹)) ^ r j /
          (Nat.factorial (r j) : ℝ) ≤
        ∏ j ∈ J,
          ∑ n ∈ cepPrimePacketProducts (P j) (r j), ((n : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        exact reciprocalPrimeSum_pow_div_factorial_le_productReciprocalSum (P j) (r j)
    _ = ∑ f ∈ cepMultiscalePacketChoices J P r,
        cepMultiscalePacketWeight J f :=
      prod_productReciprocalSum_eq_multiscalePacketWeightSum J P r

/-- Collision-free full product form of CEP (3.11), ready to feed the
multiscale smooth-number recurrence. -/
theorem prod_reciprocalPrimeSum_pow_div_factorial_le_multiscaleProductReciprocalSum
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ)
    (hinj : Set.InjOn (cepMultiscalePacketValue J)
      (cepMultiscalePacketChoices J P r)) :
    ∏ j ∈ J,
        (∑ p ∈ P j, (((p : ℕ) : ℝ)⁻¹)) ^ r j /
          (Nat.factorial (r j) : ℝ) ≤
      ∑ n ∈ cepMultiscalePacketProducts J P r, ((n : ℝ)⁻¹) := by
  rw [sum_inv_cepMultiscalePacketProducts_eq_weightSum_of_injOn J P r hinj]
  exact prod_reciprocalPrimeSum_pow_div_factorial_le_multiscalePacketWeightSum J P r

/-- Exact collision-free CEP (3.11) for pairwise disjoint finite prime bands.
No injectivity premise remains: it is discharged by unique factorization. -/
theorem prod_reciprocalPrimeSum_pow_div_factorial_le_of_disjoint
    {ι : Type*} [DecidableEq ι] {y : ℕ} (J : Finset ι)
    (P : ι → Finset (TaoBoundedPrime y)) (r : ι → ℕ)
    (hdisj : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (P j) (P k)) :
    ∏ j ∈ J,
        (∑ p ∈ P j, (((p : ℕ) : ℝ)⁻¹)) ^ r j /
          (Nat.factorial (r j) : ℝ) ≤
      ∑ n ∈ cepMultiscalePacketProducts J P r, ((n : ℝ)⁻¹) := by
  exact
    prod_reciprocalPrimeSum_pow_div_factorial_le_multiscaleProductReciprocalSum
      J P r (injOn_cepMultiscalePacketValue_of_disjoint J P r hdisj)

end

end Tao2026

import Tao2026.ErdosSelfridgePrimorial

/-!
# The first finite square cases in Erdős--Selfridge Section 3.2

The source treats lengths three and four separately before its small-prime
count for the remaining finite lengths.  At length three there are only two
possible squarefree coefficients supported below the length.  At length four,
four distinct coefficients must exhaust the positive divisors of six, whose
product is a square; the product of four consecutive integers would then be a
square, contradicting its exact difference-of-squares identity.
-/

namespace Tao2026

open scoped BigOperators

/-- Every canonical squarefree coefficient in a square-case failure divides
the product of the primes below the interval length. -/
theorem powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure
    {N H m : ℕ} (hm : m ∈ consecutiveInterval N H)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    powerFreePart 2 m ∣ erdosSelfridgePrimeProduct H := by
  let a := powerFreePart 2 m
  have haSq : Squarefree a := by
    apply Nat.squarefree_of_factorization_le_one (powerFreePart_ne_zero _ _)
    intro p
    have hp := factorization_powerFreePart_lt
      (l := 2) (n := m) (p := p) (by omega)
    omega
  have hsubset : a.primeFactors ⊆ Nat.primesBelow H := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ a := (Nat.mem_primeFactors.mp hp).2.1
    exact Nat.mem_primesBelow.mpr ⟨
      prime_dvd_powerFreePart_lt_of_large_factorization_dvd (fun q hHq hq => by
        by_cases hqDvd : q ∣ m
        · rw [← factorization_consecutiveProduct_eq_intervalElement_of_length_le
            hm hq hHq hqDvd]
          exact hfail q hHq hq
        · rw [Nat.factorization_eq_zero_of_not_dvd hqDvd]
          exact dvd_zero 2) hpPrime hpDvd,
      hpPrime⟩
  change a ∣ erdosSelfridgePrimeProduct H
  rw [erdosSelfridgePrimeProduct, ← Nat.prod_primeFactors_of_squarefree haSq]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsubset

/-- The finite candidate set for a squarefree coefficient at length `H`.
Writing it as the positive divisors of the prime product makes the small
Section 3.2 cardinality computations kernel-reducible. -/
def erdosSelfridgeSquareCoefficientCandidates (H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (erdosSelfridgePrimeProduct H)).filter
    (fun a => a ∣ erdosSelfridgePrimeProduct H)

/-- Failure plus Lemma 1 embeds all `H` canonical coefficients into the
finite candidate set of positive squarefree products of primes below `H`. -/
theorem length_le_card_erdosSelfridgeSquareCoefficientCandidates_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 3 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    H ≤ (erdosSelfridgeSquareCoefficientCandidates H).card := by
  let f : ℕ → ℕ := fun i => powerFreePart 2 (N + (i + 1))
  let A := (Finset.range H).image f
  have hinj : Set.InjOn f (Finset.range H) :=
    powerFreePart_two_injOn_range_of_failure hSS hH hHN hfail
  have hcard : A.card = H := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
  have hsubset : A ⊆ erdosSelfridgeSquareCoefficientCandidates H := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [erdosSelfridgeSquareCoefficientCandidates, Finset.mem_filter,
      Finset.mem_Icc]
    have hiInterval : N + (i + 1) ∈ consecutiveInterval N H := by
      rw [consecutiveInterval, Finset.mem_Ioc]
      have hiH := Finset.mem_range.mp hi
      omega
    have hdvd :=
      powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure
        hiInterval hfail
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
      Nat.le_of_dvd (erdosSelfridgePrimeProduct_pos H) hdvd⟩, hdvd⟩
  calc
    H = A.card := hcard.symm
    _ ≤ (erdosSelfridgeSquareCoefficientCandidates H).card :=
      Finset.card_le_card hsubset

/-- Section 3.2, `H=3`: three distinct coefficients cannot fit among the two
positive divisors of the prime product `2`. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_three
    (hSS : SylvesterSchurConclusion) {N : ℕ} (hN : 3 < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N 3 2 := by
  intro hfail
  let f : ℕ → ℕ := fun i => powerFreePart 2 (N + (i + 1))
  let A := (Finset.range 3).image f
  have hinj : Set.InjOn f (Finset.range 3) :=
    powerFreePart_two_injOn_range_of_failure hSS (by norm_num) hN hfail
  have hcard : A.card = 3 := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
  have hsubset : A ⊆ Finset.Icc 1 2 := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _)
    · have hiInterval : N + (i + 1) ∈ consecutiveInterval N 3 := by
        rw [consecutiveInterval, Finset.mem_Ioc]
        have hiH := Finset.mem_range.mp hi
        omega
      have hdvd :=
        powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure
          hiInterval hfail
      norm_num [erdosSelfridgePrimeProduct, Nat.primesBelow] at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
  have hcardLe := Finset.card_le_card hsubset
  norm_num at hcardLe
  omega

/-- Section 3.2, `H=5`: primes below the length are still only `2` and `3`,
so five distinct coefficients cannot fit among the four divisors of six. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_five
    (hSS : SylvesterSchurConclusion) {N : ℕ} (hN : 5 < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N 5 2 := by
  intro hfail
  have hcard :=
    length_le_card_erdosSelfridgeSquareCoefficientCandidates_of_failure
      hSS (N := N) (H := 5) (by norm_num) hN hfail
  have hcandidates : (erdosSelfridgeSquareCoefficientCandidates 5).card = 4 := by
    decide
  omega

@[simp]
theorem consecutiveProduct_four (N : ℕ) :
    consecutiveProduct N 4 = (N + 1) * (N + 2) * (N + 3) * (N + 4) := by
  norm_num [consecutiveProduct, consecutiveInterval,
    Finset.prod_Ioc_succ_top]

/-- Four consecutive positive integers never have square product.  This is
the source identity `(N²+5N+5)²-1`. -/
theorem not_exists_consecutiveProduct_eq_square_four (N : ℕ) :
    ¬∃ r : ℕ, consecutiveProduct N 4 = r ^ 2 := by
  rintro ⟨r, hr⟩
  rw [consecutiveProduct_four] at hr
  let s := N ^ 2 + 5 * N + 5
  have hidentity :
      (N + 1) * (N + 2) * (N + 3) * (N + 4) + 1 = s ^ 2 := by
    dsimp only [s]
    ring
  have hrpos : 0 < r := by
    by_contra h
    have : r = 0 := by omega
    subst r
    norm_num at hr
  have hrsq : r ^ 2 + 1 = s ^ 2 := by omega
  have hrs : r < s := by nlinarith
  have hrsucc : r + 1 ≤ s := by omega
  have hsquares : (r + 1) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hrsucc 2
  nlinarith

/-- Section 3.2, `H=4`: the distinct canonical coefficients are exactly
`1,2,3,6`, so their product is `6²`; equation (3) would make the interval
product a square. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_four
    (hSS : SylvesterSchurConclusion) {N : ℕ} (hN : 4 < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N 4 2 := by
  intro hfail
  let f : ℕ → ℕ := fun m => powerFreePart 2 m
  let A := (consecutiveInterval N 4).image f
  let D := (Finset.Icc 1 6).filter (fun a => a ∣ 6)
  have hscale : 4 ^ 2 < N :=
    erdosSelfridge_pow_lt_start_of_failure hSS (by norm_num) (by norm_num)
      hN hfail
  have hinj : Set.InjOn f (consecutiveInterval N 4) := by
    intro m hm n hn hmn
    have hsingletons : ({m} : Finset ℕ) = {n} := by
      exact powerFreePart_subproduct_injective
        (N := N) (H := 4) (l := 2) (r := 1)
        (S := {m}) (T := {n}) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hscale (by simpa using hm)
        (by simpa using hn) (by simp) (by simp) (by simpa using hmn)
    exact Finset.singleton_inj.mp hsingletons
  have hcard : A.card = 4 := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj]
    simp [consecutiveInterval]
  have hsubset : A ⊆ D := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hdvd :=
      powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure hm hfail
    have hprod : erdosSelfridgePrimeProduct 4 = 6 := by decide
    rw [hprod] at hdvd
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
      Nat.le_of_dvd (by norm_num) hdvd⟩, hdvd⟩
  have hDcard : D.card = 4 := by decide
  have hAD : A = D := Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hprodA : A.prod id = 36 := by
    rw [hAD]
    decide
  have hcoeff :
      (∏ m ∈ consecutiveInterval N 4, powerFreePart 2 m) = 36 := by
    rw [← hprodA]
    dsimp only [A, f]
    rw [Finset.prod_image]
    · rfl
    · exact hinj
  have hpos : ∀ m ∈ consecutiveInterval N 4, m ≠ 0 := by
    intro m hm
    have hmN := (Finset.mem_Ioc.mp hm).1
    omega
  have hdecomp := product_powerFreePart_mul_product_powerRootPart_pow
    (l := 2) (S := consecutiveInterval N 4) hpos
  have hsquare : ∃ r : ℕ, consecutiveProduct N 4 = r ^ 2 := by
    refine ⟨6 * ∏ m ∈ consecutiveInterval N 4, powerRootPart 2 m, ?_⟩
    rw [consecutiveProduct, ← hdecomp, hcoeff]
    ring
  exact not_exists_consecutiveProduct_eq_square_four N hsquare

/-- Outside the exceptional residue class, exactly five of the six positions
avoid divisibility by five. -/
theorem card_range_six_filter_not_five_dvd_add_succ
    {N : ℕ} (h5 : ¬ 5 ∣ N + 1) :
    ((Finset.range 6).filter (fun i => ¬ 5 ∣ N + (i + 1))).card = 5 := by
  have hmod : N % 5 < 5 := Nat.mod_lt N (by norm_num)
  interval_cases hN : N % 5
  · have heq : (Finset.range 6).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {0, 1, 2, 3, 5} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide
  · have heq : (Finset.range 6).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {0, 1, 2, 4, 5} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide
  · have heq : (Finset.range 6).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {0, 1, 3, 4, 5} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide
  · have heq : (Finset.range 6).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {0, 2, 3, 4, 5} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide
  · exfalso
    apply h5
    rw [Nat.dvd_iff_mod_eq_zero]
    omega

/-- In the exceptional class `5 ∣ N+1`, none of the middle four interval
elements is divisible by five. -/
theorem not_five_dvd_of_mem_consecutiveInterval_succ_four
    {N m : ℕ} (h5 : 5 ∣ N + 1)
    (hm : m ∈ consecutiveInterval (N + 1) 4) : ¬ 5 ∣ m := by
  intro h5m
  have hlower := (Finset.mem_Ioc.mp hm).1
  have hupper := (Finset.mem_Ioc.mp hm).2
  have hd : 5 ∣ m - (N + 1) := Nat.dvd_sub h5m h5
  have hdpos : 0 < m - (N + 1) := Nat.sub_pos_of_lt hlower
  have hdle := Nat.le_of_dvd hdpos hd
  omega

/-- At length six, removing candidates divisible by five leaves exactly the
four products supported on `2` and `3`. -/
def erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSix : Finset ℕ :=
  (erdosSelfridgeSquareCoefficientCandidates 6).filter (fun a => ¬ 5 ∣ a)

theorem powerFreePart_two_mem_candidatesWithoutFiveAtSix_of_failure
    {N m : ℕ} (hm : m ∈ consecutiveInterval N 6) (h5m : ¬ 5 ∣ m)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N 6 2) :
    powerFreePart 2 m ∈
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSix := by
  rw [erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSix,
    Finset.mem_filter, erdosSelfridgeSquareCoefficientCandidates,
    Finset.mem_filter, Finset.mem_Icc]
  have hdvd :=
    powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure hm hfail
  have hprod : erdosSelfridgePrimeProduct 6 = 30 := by decide
  rw [hprod] at hdvd
  have hnotFive : ¬ 5 ∣ powerFreePart 2 m := by
    intro h5a
    apply h5m
    rw [← powerFreePart_mul_powerRootPart_pow (l := 2)
      (n := m) (by
        have := (Finset.mem_Ioc.mp hm).1
        omega)]
    exact dvd_mul_of_dvd_left h5a _
  simp only [hprod]
  exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
    Nat.le_of_dvd (by norm_num) hdvd⟩, hdvd⟩, hnotFive⟩

/-- Lemma 1 gives injectivity directly on the interval elements, a convenient
form for exceptional finite subintervals. -/
theorem powerFreePart_two_injOn_consecutiveInterval_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 3 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    Set.InjOn (powerFreePart 2) (consecutiveInterval N H) := by
  have hscale : H ^ 2 < N :=
    erdosSelfridge_pow_lt_start_of_failure hSS hH (by norm_num) hHN hfail
  intro m hm n hn hmn
  have hsingletons : ({m} : Finset ℕ) = {n} := by
    exact powerFreePart_subproduct_injective
      (N := N) (H := H) (l := 2) (r := 1)
      (S := {m}) (T := {n}) hH (by norm_num)
      (by norm_num) (by norm_num) hscale (by simpa using hm)
      (by simpa using hn) (by simp) (by simp) (by simpa using hmn)
  exact Finset.singleton_inj.mp hsingletons

/-- Section 3.2, `H=6`, including the exceptional residue `5 ∣ N+1`. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_six
    (hSS : SylvesterSchurConclusion) {N : ℕ} (hN : 6 < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N 6 2 := by
  intro hfail
  by_cases h5 : 5 ∣ N + 1
  · let S := consecutiveInterval (N + 1) 4
    let A := S.image (powerFreePart 2)
    have hSsub : S ⊆ consecutiveInterval N 6 := by
      intro m hm
      dsimp only [S] at hm
      rw [consecutiveInterval, Finset.mem_Ioc] at hm ⊢
      omega
    have hinj : Set.InjOn (powerFreePart 2) S :=
      (powerFreePart_two_injOn_consecutiveInterval_of_failure
        hSS (by norm_num) hN hfail).mono hSsub
    have hcard : A.card = 4 := by
      dsimp only [A]
      rw [Finset.card_image_iff.mpr hinj]
      simp [S, consecutiveInterval]
    have hsubset : A ⊆
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSix := by
      intro a ha
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
      exact powerFreePart_two_mem_candidatesWithoutFiveAtSix_of_failure
        (hSsub hm) (not_five_dvd_of_mem_consecutiveInterval_succ_four h5 hm)
        hfail
    have hDcard :
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSix.card = 4 := by
      decide
    have hAD : A =
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSix :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hprodA : A.prod id = 36 := by
      rw [hAD]
      decide
    have hcoeff : (∏ m ∈ S, powerFreePart 2 m) = 36 := by
      rw [← hprodA]
      dsimp only [A]
      rw [Finset.prod_image]
      · rfl
      · exact hinj
    have hpos : ∀ m ∈ S, m ≠ 0 := by
      intro m hm
      have hmN := (Finset.mem_Ioc.mp hm).1
      omega
    have hdecomp := product_powerFreePart_mul_product_powerRootPart_pow
      (l := 2) (S := S) hpos
    have hsquare : ∃ r : ℕ, consecutiveProduct (N + 1) 4 = r ^ 2 := by
      refine ⟨6 * ∏ m ∈ S, powerRootPart 2 m, ?_⟩
      rw [consecutiveProduct,
        show consecutiveInterval (N + 1) 4 = S by rfl,
        ← hdecomp, hcoeff]
      ring
    exact not_exists_consecutiveProduct_eq_square_four (N + 1) hsquare
  · let G := (Finset.range 6).filter (fun i => ¬ 5 ∣ N + (i + 1))
    let f : ℕ → ℕ := fun i => powerFreePart 2 (N + (i + 1))
    let A := G.image f
    have hGcard : G.card = 5 :=
      card_range_six_filter_not_five_dvd_add_succ h5
    have hinjAll := powerFreePart_two_injOn_range_of_failure
      hSS (N := N) (H := 6) (by norm_num) hN hfail
    have hinj : Set.InjOn f G := hinjAll.mono (by
      intro i hi
      exact (Finset.mem_filter.mp hi).1)
    have hcard : A.card = 5 := by
      dsimp only [A]
      rw [Finset.card_image_iff.mpr hinj, hGcard]
    have hsubset : A ⊆
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSix := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hiData := Finset.mem_filter.mp hi
      have hiLt : i < 6 := Finset.mem_range.mp hiData.1
      have hiInterval : N + (i + 1) ∈ consecutiveInterval N 6 := by
        rw [consecutiveInterval, Finset.mem_Ioc]
        omega
      exact powerFreePart_two_mem_candidatesWithoutFiveAtSix_of_failure
        hiInterval hiData.2 hfail
    have hDcard :
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSix.card = 4 := by
      decide
    have hle := Finset.card_le_card hsubset
    omega

/-- At least five of seven consecutive positions avoid divisibility by five. -/
theorem five_le_card_range_seven_filter_not_five_dvd_add_succ
    (N : ℕ) :
    5 ≤ ((Finset.range 7).filter (fun i => ¬ 5 ∣ N + (i + 1))).card := by
  have hmod : N % 5 < 5 := Nat.mod_lt N (by norm_num)
  interval_cases hN : N % 5
  · have heq : (Finset.range 7).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {0, 1, 2, 3, 5, 6} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide
  · have heq : (Finset.range 7).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {0, 1, 2, 4, 5, 6} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide
  · have heq : (Finset.range 7).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {0, 1, 3, 4, 5, 6} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide
  · have heq : (Finset.range 7).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {0, 2, 3, 4, 5} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide
  · have heq : (Finset.range 7).filter (fun i => ¬ 5 ∣ N + (i + 1)) =
        {1, 2, 3, 4, 6} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]
      omega
    rw [heq]
    decide

/-- At length seven, removing candidates divisible by five leaves the four
products supported on `2` and `3`. -/
def erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSeven : Finset ℕ :=
  (erdosSelfridgeSquareCoefficientCandidates 7).filter (fun a => ¬ 5 ∣ a)

theorem powerFreePart_two_mem_candidatesWithoutFiveAtSeven_of_failure
    {N m : ℕ} (hm : m ∈ consecutiveInterval N 7) (h5m : ¬ 5 ∣ m)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N 7 2) :
    powerFreePart 2 m ∈
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSeven := by
  rw [erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSeven,
    Finset.mem_filter, erdosSelfridgeSquareCoefficientCandidates,
    Finset.mem_filter, Finset.mem_Icc]
  have hdvd :=
    powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure hm hfail
  have hprod : erdosSelfridgePrimeProduct 7 = 30 := by decide
  rw [hprod] at hdvd
  have hnotFive : ¬ 5 ∣ powerFreePart 2 m := by
    intro h5a
    apply h5m
    rw [← powerFreePart_mul_powerRootPart_pow (l := 2)
      (n := m) (by
        have := (Finset.mem_Ioc.mp hm).1
        omega)]
    exact dvd_mul_of_dvd_left h5a _
  simp only [hprod]
  exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
    Nat.le_of_dvd (by norm_num) hdvd⟩, hdvd⟩, hnotFive⟩

/-- Section 3.2, `H=7`: at least five coefficients avoid the prime five,
but only four squarefree products supported on `2` and `3` are available. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_seven
    (hSS : SylvesterSchurConclusion) {N : ℕ} (hN : 7 < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N 7 2 := by
  intro hfail
  let G := (Finset.range 7).filter (fun i => ¬ 5 ∣ N + (i + 1))
  let f : ℕ → ℕ := fun i => powerFreePart 2 (N + (i + 1))
  let A := G.image f
  have hGcard : 5 ≤ G.card :=
    five_le_card_range_seven_filter_not_five_dvd_add_succ N
  have hinjAll := powerFreePart_two_injOn_range_of_failure
    hSS (N := N) (H := 7) (by norm_num) hN hfail
  have hinj : Set.InjOn f G := hinjAll.mono (by
    intro i hi
    exact (Finset.mem_filter.mp hi).1)
  have hcard : A.card = G.card := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj]
  have hsubset : A ⊆
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSeven := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hiData := Finset.mem_filter.mp hi
    have hiLt : i < 7 := Finset.mem_range.mp hiData.1
    have hiInterval : N + (i + 1) ∈ consecutiveInterval N 7 := by
      rw [consecutiveInterval, Finset.mem_Ioc]
      omega
    exact powerFreePart_two_mem_candidatesWithoutFiveAtSeven_of_failure
      hiInterval hiData.2 hfail
  have hDcard :
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveAtSeven.card = 4 := by
    decide
  have hle := Finset.card_le_card hsubset
  omega

/-- Combined source-facing base of the finite Section 3.2 analysis. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seven
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 3 ≤ H) (hHupper : H ≤ 7) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  interval_cases H
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_three hSS hHN
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_four hSS hHN
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_five hSS hHN
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_six hSS hHN
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_seven hSS hHN

/-- Backward-compatible form of the release-3.04 finite endpoint. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_six
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 3 ≤ H) (hHupper : H ≤ 6) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 :=
  not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seven
    hSS hHlower (by omega) hHN

/-- Divisibility by a divisor of `35` is unchanged when the first summand is
reduced modulo `35`. -/
theorem dvd_add_iff_dvd_mod_thirty_five_add
    {d : ℕ} (hd : d ∣ 35) (N k : ℕ) :
    d ∣ N + k ↔ d ∣ N % 35 + k := by
  have heq : (N + k) % d = (N % 35 + k) % d := by
    calc
      (N + k) % d = (N % d + k % d) % d := Nat.add_mod N k d
      _ = ((N % 35) % d + k % d) % d := by
        rw [Nat.mod_mod_of_dvd N hd]
      _ = (N % 35 + k) % d := (Nat.add_mod (N % 35) k d).symm
  simp only [Nat.dvd_iff_mod_eq_zero, heq]

/-- Except in the source's exceptional length-eight congruence class, at
least five positions avoid divisibility by both five and seven. -/
theorem five_le_card_range_eight_filter_not_five_or_seven_dvd_add_succ
    {N : ℕ} (hex : ¬ (7 ∣ N + 1 ∧ 5 ∣ N + 2)) :
    5 ≤ ((Finset.range 8).filter
      (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1))).card := by
  have heq :
      (Finset.range 8).filter
          (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1)) =
        (Finset.range 8).filter
          (fun i => ¬ 5 ∣ N % 35 + (i + 1) ∧
            ¬ 7 ∣ N % 35 + (i + 1)) := by
    apply Finset.filter_congr
    intro i hi
    rw [dvd_add_iff_dvd_mod_thirty_five_add (by norm_num : 5 ∣ 35),
      dvd_add_iff_dvd_mod_thirty_five_add (by norm_num : 7 ∣ 35)]
  have hex' : ¬ (7 ∣ N % 35 + 1 ∧ 5 ∣ N % 35 + 2) := by
    simpa only [← dvd_add_iff_dvd_mod_thirty_five_add
        (by norm_num : 7 ∣ 35),
      ← dvd_add_iff_dvd_mod_thirty_five_add
        (by norm_num : 5 ∣ 35)] using hex
  rw [heq]
  have hmod : N % 35 < 35 := Nat.mod_lt N (by norm_num)
  interval_cases hN : N % 35
  all_goals try norm_num at hex'
  all_goals decide

/-- In the exceptional length-eight class, the middle four interval elements
are divisible by neither five nor seven. -/
theorem not_five_and_not_seven_dvd_of_mem_consecutiveInterval_add_two_four
    {N m : ℕ} (h7 : 7 ∣ N + 1) (h5 : 5 ∣ N + 2)
    (hm : m ∈ consecutiveInterval (N + 2) 4) : ¬ 5 ∣ m ∧ ¬ 7 ∣ m := by
  have hlower := (Finset.mem_Ioc.mp hm).1
  have hupper := (Finset.mem_Ioc.mp hm).2
  constructor
  · intro h5m
    have hd : 5 ∣ m - (N + 2) := Nat.dvd_sub h5m h5
    have hdpos : 0 < m - (N + 2) := Nat.sub_pos_of_lt hlower
    have hdle := Nat.le_of_dvd hdpos hd
    omega
  · intro h7m
    have hbase : N + 1 < m := by omega
    have hd : 7 ∣ m - (N + 1) := Nat.dvd_sub h7m h7
    have hdpos : 0 < m - (N + 1) := Nat.sub_pos_of_lt hbase
    have hdle := Nat.le_of_dvd hdpos hd
    omega

/-- At length eight, removing candidates divisible by five or seven leaves
the four products supported on `2` and `3`. -/
def erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSevenAtEight :
    Finset ℕ :=
  (erdosSelfridgeSquareCoefficientCandidates 8).filter
    (fun a => ¬ 5 ∣ a ∧ ¬ 7 ∣ a)

theorem powerFreePart_two_mem_candidatesWithoutFiveOrSevenAtEight_of_failure
    {N m : ℕ} (hm : m ∈ consecutiveInterval N 8)
    (h5m : ¬ 5 ∣ m) (h7m : ¬ 7 ∣ m)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N 8 2) :
    powerFreePart 2 m ∈
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSevenAtEight := by
  rw [erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSevenAtEight,
    Finset.mem_filter, erdosSelfridgeSquareCoefficientCandidates,
    Finset.mem_filter, Finset.mem_Icc]
  have hdvd :=
    powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure hm hfail
  have hprod : erdosSelfridgePrimeProduct 8 = 210 := by decide
  rw [hprod] at hdvd
  have hdecomp := powerFreePart_mul_powerRootPart_pow (l := 2)
    (n := m) (by
      have := (Finset.mem_Ioc.mp hm).1
      omega)
  have hnotFive : ¬ 5 ∣ powerFreePart 2 m := by
    intro h5a
    apply h5m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left h5a _
  have hnotSeven : ¬ 7 ∣ powerFreePart 2 m := by
    intro h7a
    apply h7m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left h7a _
  simp only [hprod]
  exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
    Nat.le_of_dvd (by norm_num) hdvd⟩, hdvd⟩, hnotFive, hnotSeven⟩

/-- Section 3.2, `H=8`, including the exceptional congruences
`7 ∣ N+1` and `5 ∣ N+2`. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_eight
    (hSS : SylvesterSchurConclusion) {N : ℕ} (hN : 8 < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N 8 2 := by
  intro hfail
  by_cases hex : 7 ∣ N + 1 ∧ 5 ∣ N + 2
  · let S := consecutiveInterval (N + 2) 4
    let A := S.image (powerFreePart 2)
    have hSsub : S ⊆ consecutiveInterval N 8 := by
      intro m hm
      dsimp only [S] at hm
      rw [consecutiveInterval, Finset.mem_Ioc] at hm ⊢
      omega
    have hinj : Set.InjOn (powerFreePart 2) S :=
      (powerFreePart_two_injOn_consecutiveInterval_of_failure
        hSS (by norm_num) hN hfail).mono hSsub
    have hcard : A.card = 4 := by
      dsimp only [A]
      rw [Finset.card_image_iff.mpr hinj]
      simp [S, consecutiveInterval]
    have hsubset : A ⊆
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSevenAtEight := by
      intro a ha
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
      have hav :=
        not_five_and_not_seven_dvd_of_mem_consecutiveInterval_add_two_four
          hex.1 hex.2 hm
      exact
        powerFreePart_two_mem_candidatesWithoutFiveOrSevenAtEight_of_failure
          (hSsub hm) hav.1 hav.2 hfail
    have hDcard :
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSevenAtEight.card =
          4 := by
      decide
    have hAD : A =
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSevenAtEight :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hprodA : A.prod id = 36 := by
      rw [hAD]
      decide
    have hcoeff : (∏ m ∈ S, powerFreePart 2 m) = 36 := by
      rw [← hprodA]
      dsimp only [A]
      rw [Finset.prod_image]
      · rfl
      · exact hinj
    have hpos : ∀ m ∈ S, m ≠ 0 := by
      intro m hm
      have hmN := (Finset.mem_Ioc.mp hm).1
      omega
    have hdecomp := product_powerFreePart_mul_product_powerRootPart_pow
      (l := 2) (S := S) hpos
    have hsquare : ∃ r : ℕ, consecutiveProduct (N + 2) 4 = r ^ 2 := by
      refine ⟨6 * ∏ m ∈ S, powerRootPart 2 m, ?_⟩
      rw [consecutiveProduct,
        show consecutiveInterval (N + 2) 4 = S by rfl,
        ← hdecomp, hcoeff]
      ring
    exact not_exists_consecutiveProduct_eq_square_four (N + 2) hsquare
  · let G := (Finset.range 8).filter
      (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1))
    let f : ℕ → ℕ := fun i => powerFreePart 2 (N + (i + 1))
    let A := G.image f
    have hGcard : 5 ≤ G.card :=
      five_le_card_range_eight_filter_not_five_or_seven_dvd_add_succ hex
    have hinjAll := powerFreePart_two_injOn_range_of_failure
      hSS (N := N) (H := 8) (by norm_num) hN hfail
    have hinj : Set.InjOn f G := hinjAll.mono (by
      intro i hi
      exact (Finset.mem_filter.mp hi).1)
    have hcard : A.card = G.card := by
      dsimp only [A]
      rw [Finset.card_image_iff.mpr hinj]
    have hsubset : A ⊆
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSevenAtEight := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hiData := Finset.mem_filter.mp hi
      have hiLt : i < 8 := Finset.mem_range.mp hiData.1
      have hiInterval : N + (i + 1) ∈ consecutiveInterval N 8 := by
        rw [consecutiveInterval, Finset.mem_Ioc]
        omega
      exact
        powerFreePart_two_mem_candidatesWithoutFiveOrSevenAtEight_of_failure
          hiInterval hiData.2.1 hiData.2.2 hfail
    have hDcard :
        erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSevenAtEight.card =
          4 := by
      decide
    have hle := Finset.card_le_card hsubset
    omega

/-- Combined finite Section 3.2 endpoint through length eight. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_eight
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 3 ≤ H) (hHupper : H ≤ 8) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  rcases Nat.eq_or_lt_of_le hHupper with rfl | hHlt
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_eight hSS hHN
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seven
      hSS hHlower (by omega) hHN

/-- Nine consecutive positions always contain at least five avoiding both
five and seven. -/
theorem five_le_card_range_nine_filter_not_five_or_seven_dvd_add_succ
    (N : ℕ) :
    5 ≤ ((Finset.range 9).filter
      (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1))).card := by
  have heq :
      (Finset.range 9).filter
          (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1)) =
        (Finset.range 9).filter
          (fun i => ¬ 5 ∣ N % 35 + (i + 1) ∧
            ¬ 7 ∣ N % 35 + (i + 1)) := by
    apply Finset.filter_congr
    intro i hi
    rw [dvd_add_iff_dvd_mod_thirty_five_add (by norm_num : 5 ∣ 35),
      dvd_add_iff_dvd_mod_thirty_five_add (by norm_num : 7 ∣ 35)]
  rw [heq]
  have hmod : N % 35 < 35 := Nat.mod_lt N (by norm_num)
  interval_cases hN : N % 35 <;> decide

/-- The length-nine count persists for every longer initial segment. -/
theorem five_le_card_range_filter_not_five_or_seven_dvd_add_succ
    {N H : ℕ} (hH : 9 ≤ H) :
    5 ≤ ((Finset.range H).filter
      (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1))).card := by
  apply (five_le_card_range_nine_filter_not_five_or_seven_dvd_add_succ N).trans
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_range.mpr (by
    have hi9 := Finset.mem_range.mp hi.1
    omega), hi.2⟩

/-- Candidate coefficients with the primes five and seven removed. -/
def erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSeven
    (H : ℕ) : Finset ℕ :=
  (erdosSelfridgeSquareCoefficientCandidates H).filter
    (fun a => ¬ 5 ∣ a ∧ ¬ 7 ∣ a)

theorem powerFreePart_two_mem_candidatesWithoutFiveOrSeven_of_failure
    {N H m : ℕ} (hHlower : 9 ≤ H) (hHupper : H ≤ 11)
    (hm : m ∈ consecutiveInterval N H)
    (h5m : ¬ 5 ∣ m) (h7m : ¬ 7 ∣ m)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    powerFreePart 2 m ∈
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSeven H := by
  rw [erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSeven,
    Finset.mem_filter, erdosSelfridgeSquareCoefficientCandidates,
    Finset.mem_filter, Finset.mem_Icc]
  have hdvd :=
    powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure hm hfail
  have hprod : erdosSelfridgePrimeProduct H = 210 := by
    interval_cases H <;> decide
  rw [hprod] at hdvd
  have hdecomp := powerFreePart_mul_powerRootPart_pow (l := 2)
    (n := m) (by
      have := (Finset.mem_Ioc.mp hm).1
      omega)
  have hnotFive : ¬ 5 ∣ powerFreePart 2 m := by
    intro h5a
    apply h5m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left h5a _
  have hnotSeven : ¬ 7 ∣ powerFreePart 2 m := by
    intro h7a
    apply h7m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left h7a _
  simp only [hprod]
  exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
    Nat.le_of_dvd (by norm_num) hdvd⟩, hdvd⟩, hnotFive, hnotSeven⟩

/-- Section 3.2 for the uniform lengths nine through eleven. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_nine_le_of_le_eleven
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 9 ≤ H) (hHupper : H ≤ 11) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  intro hfail
  let G := (Finset.range H).filter
    (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1))
  let f : ℕ → ℕ := fun i => powerFreePart 2 (N + (i + 1))
  let A := G.image f
  have hGcard : 5 ≤ G.card :=
    five_le_card_range_filter_not_five_or_seven_dvd_add_succ hHlower
  have hinjAll := powerFreePart_two_injOn_range_of_failure
    hSS (N := N) (H := H) (by omega) hHN hfail
  have hinj : Set.InjOn f G := hinjAll.mono (by
    intro i hi
    exact (Finset.mem_filter.mp hi).1)
  have hcard : A.card = G.card := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj]
  have hsubset : A ⊆
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSeven H := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hiData := Finset.mem_filter.mp hi
    have hiLt : i < H := Finset.mem_range.mp hiData.1
    have hiInterval : N + (i + 1) ∈ consecutiveInterval N H := by
      rw [consecutiveInterval, Finset.mem_Ioc]
      omega
    exact powerFreePart_two_mem_candidatesWithoutFiveOrSeven_of_failure
      hHlower hHupper hiInterval hiData.2.1 hiData.2.2 hfail
  have hDcard :
      (erdosSelfridgeSquareCoefficientCandidatesWithoutFiveOrSeven H).card =
        4 := by
    interval_cases H <;> decide
  have hle := Finset.card_le_card hsubset
  omega

/-- Combined finite Section 3.2 endpoint through length eleven. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_eleven
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 3 ≤ H) (hHupper : H ≤ 11) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  by_cases hH8 : H ≤ 8
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_eight
      hSS hHlower hH8 hHN
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_nine_le_of_le_eleven
      hSS (by omega) hHupper hHN

/-- Divisibility by a divisor of `385` is unchanged when the first summand is
reduced modulo `385`. -/
theorem dvd_add_iff_dvd_mod_three_eighty_five_add
    {d : ℕ} (hd : d ∣ 385) (N k : ℕ) :
    d ∣ N + k ↔ d ∣ N % 385 + k := by
  have heq : (N + k) % d = (N % 385 + k) % d := by
    calc
      (N + k) % d = (N % d + k % d) % d := Nat.add_mod N k d
      _ = ((N % 385) % d + k % d) % d := by
        rw [Nat.mod_mod_of_dvd N hd]
      _ = (N % 385 + k) % d := (Nat.add_mod (N % 385) k d).symm
  simp only [Nat.dvd_iff_mod_eq_zero, heq]

/-- Twelve consecutive positions contain at least five avoiding `5`, `7`,
and `11`. -/
theorem five_le_card_range_twelve_filter_not_five_seven_eleven_dvd_add_succ
    (N : ℕ) :
    5 ≤ ((Finset.range 12).filter
      (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1) ∧
        ¬ 11 ∣ N + (i + 1))).card := by
  have heq :
      (Finset.range 12).filter
          (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1) ∧
            ¬ 11 ∣ N + (i + 1)) =
        (Finset.range 12).filter
          (fun i => ¬ 5 ∣ N % 385 + (i + 1) ∧
            ¬ 7 ∣ N % 385 + (i + 1) ∧
            ¬ 11 ∣ N % 385 + (i + 1)) := by
    apply Finset.filter_congr
    intro i hi
    rw [dvd_add_iff_dvd_mod_three_eighty_five_add (by norm_num : 5 ∣ 385),
      dvd_add_iff_dvd_mod_three_eighty_five_add (by norm_num : 7 ∣ 385),
      dvd_add_iff_dvd_mod_three_eighty_five_add (by norm_num : 11 ∣ 385)]
  rw [heq]
  have hmod : N % 385 < 385 := Nat.mod_lt N (by norm_num)
  interval_cases hN : N % 385 <;> decide

/-- The length-twelve count persists for every longer initial segment. -/
theorem five_le_card_range_filter_not_five_seven_eleven_dvd_add_succ
    {N H : ℕ} (hH : 12 ≤ H) :
    5 ≤ ((Finset.range H).filter
      (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1) ∧
        ¬ 11 ∣ N + (i + 1))).card := by
  apply
    (five_le_card_range_twelve_filter_not_five_seven_eleven_dvd_add_succ N).trans
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_range.mpr (by
    have hi12 := Finset.mem_range.mp hi.1
    omega), hi.2⟩

/-- Candidate coefficients with the primes five, seven, and eleven removed. -/
def erdosSelfridgeSquareCoefficientCandidatesWithoutFiveSevenEleven
    (H : ℕ) : Finset ℕ :=
  (erdosSelfridgeSquareCoefficientCandidates H).filter
    (fun a => ¬ 5 ∣ a ∧ ¬ 7 ∣ a ∧ ¬ 11 ∣ a)

theorem powerFreePart_two_mem_candidatesWithoutFiveSevenEleven_of_failure
    {N H m : ℕ} (hHlower : 12 ≤ H) (hHupper : H ≤ 13)
    (hm : m ∈ consecutiveInterval N H)
    (h5m : ¬ 5 ∣ m) (h7m : ¬ 7 ∣ m) (h11m : ¬ 11 ∣ m)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    powerFreePart 2 m ∈
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveSevenEleven H := by
  rw [erdosSelfridgeSquareCoefficientCandidatesWithoutFiveSevenEleven,
    Finset.mem_filter, erdosSelfridgeSquareCoefficientCandidates,
    Finset.mem_filter, Finset.mem_Icc]
  have hdvd :=
    powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure hm hfail
  have hprod : erdosSelfridgePrimeProduct H = 2310 := by
    interval_cases H <;> decide
  rw [hprod] at hdvd
  have hdecomp := powerFreePart_mul_powerRootPart_pow (l := 2)
    (n := m) (by
      have := (Finset.mem_Ioc.mp hm).1
      omega)
  have hnotFive : ¬ 5 ∣ powerFreePart 2 m := by
    intro h5a
    apply h5m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left h5a _
  have hnotSeven : ¬ 7 ∣ powerFreePart 2 m := by
    intro h7a
    apply h7m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left h7a _
  have hnotEleven : ¬ 11 ∣ powerFreePart 2 m := by
    intro h11a
    apply h11m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left h11a _
  simp only [hprod]
  exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
    Nat.le_of_dvd (by norm_num) hdvd⟩, hdvd⟩,
    hnotFive, hnotSeven, hnotEleven⟩

/-- Section 3.2 for the uniform lengths twelve and thirteen. -/
theorem
    not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_twelve_le_of_le_thirteen
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 12 ≤ H) (hHupper : H ≤ 13) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  intro hfail
  let G := (Finset.range H).filter
    (fun i => ¬ 5 ∣ N + (i + 1) ∧ ¬ 7 ∣ N + (i + 1) ∧
      ¬ 11 ∣ N + (i + 1))
  let f : ℕ → ℕ := fun i => powerFreePart 2 (N + (i + 1))
  let A := G.image f
  have hGcard : 5 ≤ G.card :=
    five_le_card_range_filter_not_five_seven_eleven_dvd_add_succ hHlower
  have hinjAll := powerFreePart_two_injOn_range_of_failure
    hSS (N := N) (H := H) (by omega) hHN hfail
  have hinj : Set.InjOn f G := hinjAll.mono (by
    intro i hi
    exact (Finset.mem_filter.mp hi).1)
  have hcard : A.card = G.card := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj]
  have hsubset : A ⊆
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveSevenEleven H := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hiData := Finset.mem_filter.mp hi
    have hiLt : i < H := Finset.mem_range.mp hiData.1
    have hiInterval : N + (i + 1) ∈ consecutiveInterval N H := by
      rw [consecutiveInterval, Finset.mem_Ioc]
      omega
    exact powerFreePart_two_mem_candidatesWithoutFiveSevenEleven_of_failure
      hHlower hHupper hiInterval hiData.2.1 hiData.2.2.1 hiData.2.2.2 hfail
  let D := (Finset.Icc 1 6).filter (fun a => a ∣ 6)
  have hcandidates :
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveSevenEleven H ⊆ D := by
    intro a ha
    rw [erdosSelfridgeSquareCoefficientCandidatesWithoutFiveSevenEleven,
      Finset.mem_filter, erdosSelfridgeSquareCoefficientCandidates,
      Finset.mem_filter, Finset.mem_Icc] at ha
    have hprod : erdosSelfridgePrimeProduct H = 2310 := by
      interval_cases H <;> decide
    rw [hprod] at ha
    have h5c : a.Coprime 5 :=
      ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr ha.2.1).symm
    have h7c : a.Coprime 7 :=
      ((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr ha.2.2.1).symm
    have h11c : a.Coprime 11 :=
      ((show Nat.Prime 11 by norm_num).coprime_iff_not_dvd.mpr ha.2.2.2).symm
    have hc : a.Coprime (5 * 7 * 11) :=
      (h5c.mul_right h7c).mul_right h11c
    have hadvd : a ∣ (5 * 7 * 11) * 6 := by
      norm_num
      exact ha.1.2
    have hadvd6 : a ∣ 6 := hc.dvd_of_dvd_mul_left hadvd
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨ha.1.1.1, Nat.le_of_dvd (by norm_num) hadvd6⟩, hadvd6⟩
  have hDcard : D.card = 4 := by decide
  have hle := Finset.card_le_card (hsubset.trans hcandidates)
  omega

/-- Combined finite Section 3.2 endpoint through length thirteen. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_thirteen
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 3 ≤ H) (hHupper : H ≤ 13) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  by_cases hH11 : H ≤ 11
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_eleven
      hSS hHlower hH11 hHN
  · exact
      not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_twelve_le_of_le_thirteen
        hSS (by omega) hHupper hHN

end Tao2026

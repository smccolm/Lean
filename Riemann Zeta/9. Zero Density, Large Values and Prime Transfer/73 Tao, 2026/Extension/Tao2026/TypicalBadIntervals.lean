import Tao2026.BadIntervalMaximal

/-!
# Typical normalized bad intervals

This module gives exact finite contracts for the normalized and typical
intervals in Definitions 6.3--6.4 of Tao's argument.  The source's slowly
varying expressions `z^(1-o(1))` and `z^(1+o(1))` are represented by explicit
natural-number cutoffs.  Thus no asymptotic notation is hidden in a finite
predicate: later estimates must provide the appropriate cutoff functions.

Because the same-window admissibility claim in Lemma 6.2 does not follow from
containment, the base predicate uses the corrected comparable-scale bounds
proved in `NormalizedBadIntervals` and used by `BadIntervalMaximal`.
-/

namespace Tao2026

open scoped BigOperators

/-- Condition (ii) in the definition of a typical normalized interval: no
element of the interval is divisible by the square of an integer at least the
specified threshold. -/
def AvoidsSquareMultiplesAtLeast (N H squareThreshold : ℕ) : Prop :=
  ∀ n ∈ consecutiveInterval N H, ∀ d : ℕ,
    squareThreshold ≤ d → ¬d ^ 2 ∣ n

/-- The exact finite 1000-prime anatomy in condition (iii).  Indices
`0,...,999` represent the source's `p₁,...,p₁₀₀₀`; consequently `factors` is
nonincreasing. -/
structure TypicalPrimeAnatomy
    (lowerPrime upperPrime p₀ m : ℕ) where
  factors : Fin 1000 → ℕ
  remainder : ℕ
  factors_prime : ∀ i, (factors i).Prime
  factors_nonincreasing : ∀ ⦃i j : Fin 1000⦄, i ≤ j → factors j ≤ factors i
  lower_le_last : lowerPrime ≤ factors (Fin.last 999)
  first_le_p₀ : factors 0 ≤ p₀
  p₀_le_upper : p₀ ≤ upperPrime
  factorization : m = (∏ i, factors i) * remainder
  remainder_smooth : IsSmooth remainder (factors (Fin.last 999))

/-- The three finite conditions defining typicality, separated from the
normalized-interval base predicate so that "non-typical" is its literal
negation. -/
def SatisfiesTypicalNormalizedConditions
    (lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ m : ℕ) : Prop :=
  H < lengthCutoff ∧
    AvoidsSquareMultiplesAtLeast N H squareThreshold ∧
    Nonempty (TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)

/-- Corrected-scale exact form of a typical normalized bad interval.  The
distinguished squared prime and its cofactor are retained as named data. -/
def IsTypicalScaleNormalizedBadInterval
    (x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ) : Prop :=
  IsNormalizedBadInterval N H p₀ k m ∧
    x ≤ 4 * N + 1 ∧ N + H ≤ 2 * x ∧
    SatisfiesTypicalNormalizedConditions
      lengthCutoff squareThreshold lowerPrime upperPrime N H p₀ m

/-- A normalized interval is non-typical precisely when at least one of the
three typicality conditions fails. -/
def IsNonTypicalScaleNormalizedBadInterval
    (x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ) : Prop :=
  IsNormalizedBadInterval N H p₀ k m ∧
    x ≤ 4 * N + 1 ∧ N + H ≤ 2 * x ∧
    ¬SatisfiesTypicalNormalizedConditions
      lengthCutoff squareThreshold lowerPrime upperPrime N H p₀ m

/-- The source subsequently fixes the orientation whose distinguished value
is the left endpoint. -/
def IsForwardTypicalScaleNormalizedBadInterval
    (x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ) : Prop :=
  IsTypicalScaleNormalizedBadInterval x lengthCutoff squareThreshold
    lowerPrime upperPrime N H p₀ k m ∧ k = N + 1

/-- Every corrected-scale normalized interval is exactly typical or
non-typical for any fixed choice of finite cutoffs. -/
theorem typical_or_nonTypical_of_scaleNormalized
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (hnorm : IsNormalizedBadInterval N H p₀ k m)
    (hleft : x ≤ 4 * N + 1) (hright : N + H ≤ 2 * x) :
    IsTypicalScaleNormalizedBadInterval x lengthCutoff squareThreshold
        lowerPrime upperPrime N H p₀ k m ∨
      IsNonTypicalScaleNormalizedBadInterval x lengthCutoff squareThreshold
        lowerPrime upperPrime N H p₀ k m := by
  by_cases htyp : SatisfiesTypicalNormalizedConditions
      lengthCutoff squareThreshold lowerPrime upperPrime N H p₀ m
  · exact Or.inl ⟨hnorm, hleft, hright, htyp⟩
  · exact Or.inr ⟨hnorm, hleft, hright, htyp⟩

/-- Exact three-way split used by Proposition 6.5: a non-typical interval is
too long, contains a forbidden large square multiple, or lacks the required
1000-prime anatomy. -/
theorem IsNonTypicalScaleNormalizedBadInterval.failure_cases
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (hnon : IsNonTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    lengthCutoff ≤ H ∨
      ¬AvoidsSquareMultiplesAtLeast N H squareThreshold ∨
      ¬Nonempty (TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) := by
  have hfail := hnon.2.2.2
  simp only [SatisfiesTypicalNormalizedConditions, not_and_or] at hfail
  rcases hfail with hlength | hsquare | hanatomy
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl hsquare)
  · exact Or.inr (Or.inr hanatomy)

theorem IsTypicalScaleNormalizedBadInterval.length_lt
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (htyp : IsTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    H < lengthCutoff :=
  htyp.2.2.2.1

theorem IsTypicalScaleNormalizedBadInterval.avoidsSquareMultiples
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (htyp : IsTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    AvoidsSquareMultiplesAtLeast N H squareThreshold :=
  htyp.2.2.2.2.1

/-- Condition (ii), applied to the distinguished value `p₀²m`, forces
`p₀` below the square threshold.  This is the exact step yielding `p₀ < z³`
in the proof of Proposition 6.5. -/
theorem IsTypicalScaleNormalizedBadInterval.p₀_lt_squareThreshold
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (htyp : IsTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    p₀ < squareThreshold := by
  obtain ⟨_hH, _hbad, _hp, _hHltp, _hpMax, hk, _hmSmooth, hkm,
    _hkEndpoint, _hpow⟩ := htyp.1
  by_contra hnot
  have hthreshold : squareThreshold ≤ p₀ := by omega
  have hpSq : p₀ ^ 2 ∣ k := by
    rw [hkm]
    exact dvd_mul_right (p₀ ^ 2) m
  exact htyp.avoidsSquareMultiples k hk p₀ hthreshold hpSq

theorem TypicalPrimeAnatomy.lower_le_factor
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (i : Fin 1000) : lowerPrime ≤ a.factors i := by
  exact a.lower_le_last.trans
    (a.factors_nonincreasing (Fin.le_last i))

theorem TypicalPrimeAnatomy.factor_le_p₀
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (i : Fin 1000) : a.factors i ≤ p₀ := by
  exact (a.factors_nonincreasing (Fin.zero_le i)).trans a.first_le_p₀

theorem TypicalPrimeAnatomy.lower_le_p₀
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    lowerPrime ≤ p₀ :=
  (a.lower_le_factor 0).trans a.first_le_p₀

theorem TypicalPrimeAnatomy.factor_le_upper
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (i : Fin 1000) : a.factors i ≤ upperPrime :=
  (a.factor_le_p₀ i).trans a.p₀_le_upper

/-- The selected product of 1000 primes divides the smooth cofactor `m`. -/
theorem TypicalPrimeAnatomy.factorProduct_dvd
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    (∏ i, a.factors i) ∣ m := by
  exact ⟨a.remainder, a.factorization⟩

theorem TypicalPrimeAnatomy.factorProduct_pos
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    0 < ∏ i, a.factors i := by
  exact Finset.prod_pos fun i _hi => (a.factors_prime i).pos

set_option maxRecDepth 4000 in
/-- If a smooth cofactor has at least 1000 prime factors at or above the
lower cutoff, counted with multiplicity, its 1000 largest factors and the
remaining factorization construct condition (iii) exactly. -/
theorem exists_typicalPrimeAnatomy_of_many_large_primeFactors
    {lowerPrime upperPrime p₀ m : ℕ}
    (hmSmooth : IsSmooth m p₀) (hp₀Upper : p₀ ≤ upperPrime)
    (hcount : 1000 ≤
      (m.primeFactorsList.filter fun q => lowerPrime ≤ q).length) :
    Nonempty (TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) := by
  have hm0 : m ≠ 0 := (isSmooth_iff.mp hmSmooth).1
  let highAsc := m.primeFactorsList.filter fun q => lowerPrime ≤ q
  let highDesc := highAsc.reverse
  let selected := highDesc.take 1000
  let low := m.primeFactorsList.filter fun q => !(lowerPrime ≤ q)
  have hhighLen : 1000 ≤ highDesc.length := by
    simpa [highDesc, highAsc] using hcount
  have hselectedLen : selected.length = 1000 := by
    simp [selected, hhighLen]
  let factors : Fin 1000 → ℕ := fun i =>
    selected.get (Fin.cast hselectedLen.symm i)
  let remainder := (highDesc.drop 1000 ++ low).prod
  have hhighSorted : highDesc.SortedGE := by
    exact ((Nat.primeFactorsList_sorted m).pairwise.filter _).sortedLE.reverse
  have hselectedSorted : selected.SortedGE :=
    (hhighSorted.pairwise.take).sortedGE
  have hfactorMemHigh (i : Fin 1000) : factors i ∈ highDesc := by
    apply List.take_subset 1000 highDesc
    exact selected.get_mem (Fin.cast hselectedLen.symm i)
  have hfactorMemOriginal (i : Fin 1000) :
      factors i ∈ m.primeFactorsList := by
    have hi := hfactorMemHigh i
    dsimp only [highDesc, highAsc] at hi
    rw [List.mem_reverse] at hi
    exact List.mem_of_mem_filter hi
  have hfactorPrime (i : Fin 1000) : (factors i).Prime :=
    Nat.prime_of_mem_primeFactorsList (hfactorMemOriginal i)
  have hfactorLower (i : Fin 1000) : lowerPrime ≤ factors i := by
    have hi := hfactorMemHigh i
    dsimp only [highDesc, highAsc] at hi
    rw [List.mem_reverse] at hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  have hfactorLeP₀ (i : Fin 1000) : factors i ≤ p₀ := by
    have hi := (Nat.mem_primeFactorsList hm0).mp (hfactorMemOriginal i)
    exact (isSmooth_iff.mp hmSmooth).2 _ hi.1 hi.2
  have hfactorNonincreasing :
      ∀ ⦃i j : Fin 1000⦄, i ≤ j → factors j ≤ factors i := by
    intro i j hij
    apply hselectedSorted.antitone_get
    exact hij
  have hfactorProduct : (∏ i, factors i) = selected.prod := by
    rw [← List.prod_ofFn]
    congr 1
    apply List.ext_get
    · simp only [List.length_ofFn]
      exact hselectedLen.symm
    · intro n hnFn hnSelected
      simp only [List.length_ofFn] at hnFn
      simp only [List.get_ofFn]
      dsimp only [factors]
      congr
  have hpartition : (highAsc ++ low).Perm m.primeFactorsList := by
    exact List.filter_append_perm (fun q => lowerPrime ≤ q) m.primeFactorsList
  have hfactorization : m = (∏ i, factors i) * remainder := by
    have hsplit := List.prod_take_mul_prod_drop highDesc 1000
    have hreverse : highDesc.prod = highAsc.prod := by
      simp [highDesc]
    have hpartitionProd : highAsc.prod * low.prod = m := by
      calc
        highAsc.prod * low.prod = (highAsc ++ low).prod := by simp
        _ = m.primeFactorsList.prod := hpartition.prod_eq
        _ = m := Nat.prod_primeFactorsList hm0
    rw [hfactorProduct]
    dsimp only [remainder]
    simp only [List.prod_append]
    calc
      m = highAsc.prod * low.prod := hpartitionProd.symm
      _ = highDesc.prod * low.prod := by rw [hreverse]
      _ = (selected.prod * (highDesc.drop 1000).prod) * low.prod := by
        rw [hsplit]
      _ = selected.prod * ((highDesc.drop 1000).prod * low.prod) := by
        rw [Nat.mul_assoc]
  have hremainingPrime : ∀ a ∈ highDesc.drop 1000 ++ low, a.Prime := by
    intro a ha
    have haOriginal : a ∈ m.primeFactorsList := by
      rcases List.mem_append.mp ha with haHigh | haLow
      · have haHigh' := List.mem_of_mem_drop haHigh
        dsimp only [highDesc, highAsc] at haHigh'
        rw [List.mem_reverse] at haHigh'
        exact List.mem_of_mem_filter haHigh'
      · dsimp only [low] at haLow
        exact List.mem_of_mem_filter haLow
    exact Nat.prime_of_mem_primeFactorsList haOriginal
  have hremainderPos : 0 < remainder := by
    dsimp only [remainder]
    apply Nat.pos_of_ne_zero
    apply List.prod_ne_zero
    intro hzero
    exact (hremainingPrime 0 hzero).ne_zero rfl
  have hlastLower : lowerPrime ≤ factors (Fin.last 999) :=
    hfactorLower _
  have hdropLeLast : ∀ a ∈ highDesc.drop 1000,
      a ≤ factors (Fin.last 999) := by
    intro a ha
    have hidx : (highDesc.drop 1000).idxOf a <
        (highDesc.drop 1000).length :=
      List.idxOf_lt_length_iff.mpr ha
    have hidxHigh : 1000 + (highDesc.drop 1000).idxOf a < highDesc.length := by
      simp only [List.length_drop] at hidx
      omega
    have h999 : 999 < highDesc.length := by omega
    have hsorted := hhighSorted.getElem_ge_getElem_of_le
      (i := 1000 + (highDesc.drop 1000).idxOf a) (j := 999)
      (hi := hidxHigh) (hj := h999) (by omega)
    have haGet : highDesc[1000 + (highDesc.drop 1000).idxOf a] = a := by
      rw [← List.getElem_drop]
      exact List.getElem_idxOf hidx
    have hlastGet : highDesc[999] = factors (Fin.last 999) := by
      change highDesc[999] = selected.get
        (Fin.cast hselectedLen.symm (Fin.last 999))
      rw [List.get_eq_getElem, List.getElem_take]
      congr
    simpa only [haGet, hlastGet] using hsorted
  have hremainderSmooth : IsSmooth remainder (factors (Fin.last 999)) := by
    rw [isSmooth_iff]
    refine ⟨hremainderPos.ne', ?_⟩
    intro q hqPrime hqDvd
    obtain ⟨a, ha, hqa⟩ := hqPrime.prime.dvd_prod_iff.mp hqDvd
    have haPrime := hremainingPrime a ha
    have hqaEq : q = a := by
      rcases (Nat.dvd_prime haPrime).mp hqa with hqOne | hqaEq
      · exact (hqPrime.ne_one hqOne).elim
      · exact hqaEq
    rw [hqaEq]
    rcases List.mem_append.mp ha with haHigh | haLow
    · exact hdropLeLast a haHigh
    · have haLt : a < lowerPrime := by
        dsimp only [low] at haLow
        have hnot : ¬ lowerPrime ≤ a := by
          simpa using (List.mem_filter.mp haLow).2
        omega
      exact haLt.le.trans hlastLower
  exact ⟨{
    factors := factors
    remainder := remainder
    factors_prime := hfactorPrime
    factors_nonincreasing := hfactorNonincreasing
    lower_le_last := hlastLower
    first_le_p₀ := hfactorLeP₀ 0
    p₀_le_upper := hp₀Upper
    factorization := hfactorization
    remainder_smooth := hremainderSmooth }⟩

/-- Contrapositive form used by Proposition 6.5: failure of condition (iii)
forces fewer than 1000 prime factors above the lower cutoff. -/
theorem primeFactorsList_filter_length_lt_of_no_typicalPrimeAnatomy
    {lowerPrime upperPrime p₀ m : ℕ}
    (hmSmooth : IsSmooth m p₀) (hp₀Upper : p₀ ≤ upperPrime)
    (hno : ¬ Nonempty (TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)) :
    (m.primeFactorsList.filter fun q => lowerPrime ≤ q).length < 1000 := by
  by_contra hnot
  exact hno (exists_typicalPrimeAnatomy_of_many_large_primeFactors
    hmSmooth hp₀Upper (by omega))

/-- Once the length and square conditions hold, every non-typical interval
with `p₀` below the supplied upper cutoff is in the deficient-large-factor
branch: its smooth cofactor has fewer than 1000 prime factors at or above the
lower cutoff, counted with multiplicity. -/
theorem IsNonTypicalScaleNormalizedBadInterval.few_large_primeFactors
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (hnon : IsNonTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m)
    (hshort : H < lengthCutoff)
    (havoid : AvoidsSquareMultiplesAtLeast N H squareThreshold)
    (hp₀Upper : p₀ ≤ upperPrime) :
    (m.primeFactorsList.filter fun q => lowerPrime ≤ q).length < 1000 := by
  have hno : ¬ Nonempty
      (TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) := by
    rcases hnon.failure_cases with hlong | hsquare | hanatomy
    · omega
    · exact (hsquare havoid).elim
    · exact hanatomy
  obtain ⟨_hH, _hbad, _hpPrime, _hHltp, _hpMax, _hkMem, hmSmooth,
    _hkEq, _hkEndpoint, _hpow⟩ := hnon.1
  exact primeFactorsList_filter_length_lt_of_no_typicalPrimeAnatomy
    hmSmooth hp₀Upper hno

/-- Exact factorization packet for Tao's deficient condition-(iii) branch.
The list retains multiplicity, contains fewer than 1000 large prime factors,
and the complementary factor is smooth at the lower cutoff. -/
structure DeficientPrimeFactorization (lowerPrime p₀ m : ℕ) where
  largeFactors : List ℕ
  remainder : ℕ
  largeFactors_length_lt : largeFactors.length < 1000
  largeFactors_prime : ∀ q ∈ largeFactors, q.Prime
  lower_le_largeFactors : ∀ q ∈ largeFactors, lowerPrime ≤ q
  largeFactors_le_p₀ : ∀ q ∈ largeFactors, q ≤ p₀
  factorization : m = largeFactors.prod * remainder
  remainder_smooth : IsSmooth remainder lowerPrime

/-- The canonical filter partition of the prime-factor list realizes the
deficient factorization packet. -/
theorem exists_deficientPrimeFactorization
    {lowerPrime p₀ m : ℕ} (hmSmooth : IsSmooth m p₀)
    (hfew : (m.primeFactorsList.filter fun q => lowerPrime ≤ q).length < 1000) :
    Nonempty (DeficientPrimeFactorization lowerPrime p₀ m) := by
  have hm0 : m ≠ 0 := (isSmooth_iff.mp hmSmooth).1
  let large := m.primeFactorsList.filter fun q => lowerPrime ≤ q
  let small := m.primeFactorsList.filter fun q => !(lowerPrime ≤ q)
  have hlargePrime : ∀ q ∈ large, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactorsList
      (List.mem_of_mem_filter (by simpa only [large] using hq))
  have hlargeLower : ∀ q ∈ large, lowerPrime ≤ q := by
    intro q hq
    have hq' : q ∈ m.primeFactorsList.filter fun q => lowerPrime ≤ q := by
      simpa only [large] using hq
    exact of_decide_eq_true (List.mem_filter.mp hq').2
  have hlargeUpper : ∀ q ∈ large, q ≤ p₀ := by
    intro q hq
    have hqOriginal : q ∈ m.primeFactorsList := by
      apply List.mem_of_mem_filter
      simpa only [large] using hq
    have hqData := (Nat.mem_primeFactorsList hm0).mp hqOriginal
    exact (isSmooth_iff.mp hmSmooth).2 q hqData.1 hqData.2
  have hsmallPrime : ∀ q ∈ small, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactorsList
      (List.mem_of_mem_filter (by simpa only [small] using hq))
  have hsmallLt : ∀ q ∈ small, q < lowerPrime := by
    intro q hq
    have hq' : q ∈ m.primeFactorsList.filter fun q => !(lowerPrime ≤ q) := by
      simpa only [small] using hq
    have hnot : ¬ lowerPrime ≤ q := by
      simpa using (List.mem_filter.mp hq').2
    omega
  have hsmallPos : 0 < small.prod := by
    apply Nat.pos_of_ne_zero
    apply List.prod_ne_zero
    intro hzero
    exact (hsmallPrime 0 hzero).ne_zero rfl
  have hsmallSmooth : IsSmooth small.prod lowerPrime := by
    rw [isSmooth_iff]
    refine ⟨hsmallPos.ne', ?_⟩
    intro q hqPrime hqDvd
    obtain ⟨a, ha, hqa⟩ := hqPrime.prime.dvd_prod_iff.mp hqDvd
    have haPrime := hsmallPrime a ha
    have hqaEq : q = a := by
      rcases (Nat.dvd_prime haPrime).mp hqa with hqOne | hqaEq
      · exact (hqPrime.ne_one hqOne).elim
      · exact hqaEq
    rw [hqaEq]
    exact (hsmallLt a ha).le
  have hpartition : (large ++ small).Perm m.primeFactorsList := by
    exact List.filter_append_perm (fun q => lowerPrime ≤ q) m.primeFactorsList
  have hfactorization : m = large.prod * small.prod := by
    calc
      m = m.primeFactorsList.prod := (Nat.prod_primeFactorsList hm0).symm
      _ = (large ++ small).prod := hpartition.prod_eq.symm
      _ = large.prod * small.prod := List.prod_append
  exact ⟨{
    largeFactors := large
    remainder := small.prod
    largeFactors_length_lt := by simpa only [large] using hfew
    largeFactors_prime := hlargePrime
    lower_le_largeFactors := hlargeLower
    largeFactors_le_p₀ := hlargeUpper
    factorization := hfactorization
    remainder_smooth := hsmallSmooth }⟩

/-- A remaining non-typical interval therefore comes with Tao's exact
`m=p₁⋯pⱼ m'`, `j<1000`, `m'`-smooth factorization packet. -/
theorem IsNonTypicalScaleNormalizedBadInterval.exists_deficientPrimeFactorization
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (hnon : IsNonTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m)
    (hshort : H < lengthCutoff)
    (havoid : AvoidsSquareMultiplesAtLeast N H squareThreshold)
    (hp₀Upper : p₀ ≤ upperPrime) :
    Nonempty (DeficientPrimeFactorization lowerPrime p₀ m) := by
  obtain ⟨_hH, _hbad, _hpPrime, _hHltp, _hpMax, _hkMem, hmSmooth,
    _hkEq, _hkEndpoint, _hpow⟩ := hnon.1
  exact Tao2026.exists_deficientPrimeFactorization hmSmooth
    (hnon.few_large_primeFactors hshort havoid hp₀Upper)

/-- Exact division-form consequence displayed after Definition 6.4 in the
source: `m' ≤ 2x/(p₀² p₁...p₁₀₀₀)`. -/
theorem IsTypicalScaleNormalizedBadInterval.exists_anatomy_with_remainder_bound
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (htyp : IsTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    ∃ a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m,
      a.remainder ≤ 2 * x / (p₀ ^ 2 * ∏ i, a.factors i) := by
  obtain ⟨a⟩ := htyp.2.2.2.2.2
  refine ⟨a, ?_⟩
  obtain ⟨_hH, _hbad, hp₀, _hHltp, _hpMax, hk, _hmSmooth, hkm,
    _hkEndpoint, _hpow⟩ := htyp.1
  have hkUpper : k ≤ N + H := (Finset.mem_Ioc.mp hk).2
  have hkTwoX : k ≤ 2 * x := hkUpper.trans htyp.2.2.1
  have hkEq :
      k = (p₀ ^ 2 * ∏ i, a.factors i) * a.remainder := by
    calc
      k = p₀ ^ 2 * m := hkm
      _ = p₀ ^ 2 * ((∏ i, a.factors i) * a.remainder) :=
        congrArg (fun t => p₀ ^ 2 * t) a.factorization
      _ = (p₀ ^ 2 * ∏ i, a.factors i) * a.remainder := by
        rw [Nat.mul_assoc]
  have hmul :
      (p₀ ^ 2 * ∏ i, a.factors i) * a.remainder ≤ 2 * x := by
    rw [← hkEq]
    exact hkTwoX
  have hdenom : 0 < p₀ ^ 2 * ∏ i, a.factors i :=
    Nat.mul_pos (pow_pos hp₀.pos 2) a.factorProduct_pos
  rw [Nat.le_div_iff_mul_le hdenom]
  simpa only [Nat.mul_comm] using hmul

end Tao2026

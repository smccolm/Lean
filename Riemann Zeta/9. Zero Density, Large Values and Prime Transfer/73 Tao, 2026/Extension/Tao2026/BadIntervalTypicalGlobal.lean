import Tao2026.BadIntervalTypicalMultiplicity

/-!
# Global enlarged counting family over all ordered scales

This module assembles the enlarged remainder families over the complete
finite ordered dyadic grid.  It proves that the selected tail primes are the
top 1000 prime factors of the cofactor below the distinguished square.  This
canonical characterization makes the fixed-scale fiber argument uniform
across different scale tuples.
-/

namespace Tao2026

open Filter
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

-- Lean 4.30's symbol-frequency exporter starts a fresh meta context with the
-- default recursion limit.  Initialize its cache before the deeply dependent
-- global fiber declarations below are added to the environment.
run_meta
  discard <| Lean.LibrarySuggestions.localSymbolFrequency `Nat

-- The dependent subtype signature of this one theorem also exceeds that
-- exporter's default recursion limit.  Omitting it from premise suggestions
-- leaves the declaration and kernel proof unchanged.
run_meta
  Lean.MonadEnv.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "taoPrimeTupleGlobalTailCodeEmbedding_injective"

/-- Dyadic lower endpoints attached to an exponent tuple. -/
def taoPrimeTupleDyadicScales (R : Fin 1001 → ℕ) : Fin 1001 → ℕ :=
  fun j => 2 ^ R j

theorem antitone_taoPrimeTupleDyadicScales {R : Fin 1001 → ℕ}
    (hR : Antitone R) : Antitone (taoPrimeTupleDyadicScales R) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num) (hR hij)

/-- Once the moving lower cutoff is at least two, every retained dyadic
exponent is positive. -/
theorem one_le_of_mem_taoPrimeTupleSlowDyadicExponents
    {q : ℕ → ℕ} {x r : ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x)
    (hr : r ∈ taoPrimeTupleSlowDyadicExponents q x) : 1 ≤ r := by
  have hmeet := (mem_taoPrimeTupleSlowDyadicExponents.mp hr).2
  by_contra hr0
  have : r = 0 := by omega
  subst r
  norm_num at hmeet
  omega

theorem two_le_taoPrimeTupleDyadicScales_last_of_mem
    {q : ℕ → ℕ} {x : ℕ} {R : Fin 1001 → ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x)
    (hR : R ∈ taoPrimeTupleSlowScaleExponentTuples q x) :
    2 ≤ taoPrimeTupleDyadicScales R (Fin.last 1000) := by
  unfold taoPrimeTupleDyadicScales
  have hr : 1 ≤ R (Fin.last 1000) :=
    one_le_of_mem_taoPrimeTupleSlowDyadicExponents hlower
      ((mem_taoPrimeTupleSlowScaleExponentTuples.mp hR) (Fin.last 1000))
  calc
    2 = 2 ^ (1 : ℕ) := by norm_num
    _ ≤ 2 ^ R (Fin.last 1000) :=
      Nat.pow_le_pow_right (by norm_num) hr

/-- Enlarged representations summed over every ordered dyadic scale tuple. -/
def taoPrimeTupleGlobalEnlargedRemainderPairs
    (q : ℕ → ℕ) (x : ℕ) :
    Finset (Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple) :=
  (taoPrimeTupleSlowOrderedScaleExponentTuples q x).sigma fun R =>
    taoPrimeTupleEnlargedRemainderPairs (taoPrimeTupleDyadicScales R) x

theorem mem_taoPrimeTupleGlobalEnlargedRemainderPairs
    {q : ℕ → ℕ} {x : ℕ}
    {a : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple} :
    a ∈ taoPrimeTupleGlobalEnlargedRemainderPairs q x ↔
      a.1 ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x ∧
        a.2 ∈ taoPrimeTupleEnlargedRemainderPairs
          (taoPrimeTupleDyadicScales a.1) x := by
  simp [taoPrimeTupleGlobalEnlargedRemainderPairs]

theorem card_taoPrimeTupleGlobalEnlargedRemainderPairs
    (q : ℕ → ℕ) (x : ℕ) :
    (taoPrimeTupleGlobalEnlargedRemainderPairs q x).card =
      ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        (taoPrimeTupleEnlargedRemainderPairs
          (taoPrimeTupleDyadicScales R) x).card := by
  rw [taoPrimeTupleGlobalEnlargedRemainderPairs, Finset.card_sigma]

/-- Evaluation of a global enlarged representation. -/
def taoPrimeTupleGlobalEnlargedRemainderValue
    (a : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple) : ℕ :=
  taoPrimeTupleEnlargedRemainderValue a.2

/-- A concrete list of the 1000 selected tail coordinates. -/
def taoPrimeTupleTailList (ω : TaoPrimeTuple) : List ℕ :=
  ((Finset.univ.erase (0 : Fin 1001)).toList.map ω)

theorem prod_taoPrimeTupleTailList (ω : TaoPrimeTuple) :
    (taoPrimeTupleTailList ω).prod = taoPrimeTupleTailProduct ω := by
  simp [taoPrimeTupleTailList, taoPrimeTupleTailProduct]

theorem length_taoPrimeTupleTailList (ω : TaoPrimeTuple) :
    (taoPrimeTupleTailList ω).length = 1000 := by
  simp [taoPrimeTupleTailList]

theorem prime_of_mem_taoPrimeTupleTailList
    {P : Fin 1001 → ℕ} {ω : TaoPrimeTuple}
    (hω : ω ∈ taoPrimeTupleEnlargedSupport P)
    {p : ℕ} (hp : p ∈ taoPrimeTupleTailList ω) : p.Prime := by
  rw [taoPrimeTupleTailList, List.mem_map] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  exact mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp hω) j) |>.1

theorem perm_taoPrimeTupleTailList_primeFactorsList
    {P : Fin 1001 → ℕ} {ω : TaoPrimeTuple}
    (hω : ω ∈ taoPrimeTupleEnlargedSupport P) :
    (taoPrimeTupleTailList ω).Perm
      (taoPrimeTupleTailProduct ω).primeFactorsList := by
  apply Nat.primeFactorsList_unique (prod_taoPrimeTupleTailList ω)
  intro p hp
  exact prime_of_mem_taoPrimeTupleTailList hω hp

theorem length_primeFactorsList_taoPrimeTupleTailProduct
    {P : Fin 1001 → ℕ} {ω : TaoPrimeTuple}
    (hω : ω ∈ taoPrimeTupleEnlargedSupport P) :
    (taoPrimeTupleTailProduct ω).primeFactorsList.length = 1000 := by
  have hlen := (perm_taoPrimeTupleTailList_primeFactorsList hω).length_eq
  rw [length_taoPrimeTupleTailList] at hlen
  exact hlen.symm

/-- In one enlarged representation, unique factorization is already sorted
as the smooth remainder factors followed by the selected tail factors. -/
theorem primeFactorsList_taoPrimeTupleEnlargedCofactor_eq
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {x : ℕ} {a : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x) :
    (taoPrimeTupleTailProduct a.2 * a.1).primeFactorsList =
      a.1.primeFactorsList ++
        (taoPrimeTupleTailProduct a.2).primeFactorsList := by
  have haData := mem_taoPrimeTupleEnlargedRemainderPairs.mp ha
  have hm0 := (isSmooth_iff.mp
    (mem_taoPrimeTupleSmoothRemainders.mp haData.1).2).1
  have htail0 : taoPrimeTupleTailProduct a.2 ≠ 0 := by
    unfold taoPrimeTupleTailProduct
    exact Finset.prod_ne_zero_iff.mpr fun j hj =>
      (mem_taoDyadicPrimeBand.mp
        ((mem_taoPrimeTupleEnlargedSupport.mp haData.2) j)).1.ne_zero
  have hsorted :
      (a.1.primeFactorsList ++
        (taoPrimeTupleTailProduct a.2).primeFactorsList).SortedLE := by
    rw [List.sortedLE_iff_pairwise, List.pairwise_append]
    refine ⟨(Nat.primeFactorsList_sorted a.1).pairwise,
      (Nat.primeFactorsList_sorted
        (taoPrimeTupleTailProduct a.2)).pairwise, ?_⟩
    intro q hq p hp
    have hqPrime := Nat.prime_of_mem_primeFactorsList hq
    have hqDvd := Nat.dvd_of_mem_primeFactorsList hq
    have hqLe := (isSmooth_iff.mp
      (mem_taoPrimeTupleSmoothRemainders.mp haData.1).2).2 q hqPrime hqDvd
    have hpPrime := Nat.prime_of_mem_primeFactorsList hp
    have hpDvd := Nat.dvd_of_mem_primeFactorsList hp
    unfold taoPrimeTupleTailProduct at hpDvd
    obtain ⟨j, hj, hpj⟩ :=
      (Prime.dvd_finsetProd_iff hpPrime.prime a.2).mp hpDvd
    have hajPrime := mem_taoDyadicPrimeBand.mp
      ((mem_taoPrimeTupleEnlargedSupport.mp haData.2) j) |>.1
    have hpEq : p = a.2 j :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hajPrime).mp hpj
    have hj0 := (Finset.mem_erase.mp hj).1
    exact hqLe.trans (by
      rw [hpEq]
      exact (taoPrimeTupleRemainderSmoothnessCutoff_lt_enlarged_tail
        hPmono hlast haData.2 hj0).le)
  have hperm :
      (taoPrimeTupleTailProduct a.2 * a.1).primeFactorsList.Perm
        (a.1.primeFactorsList ++
          (taoPrimeTupleTailProduct a.2).primeFactorsList) :=
    by simpa only [Nat.mul_comm] using
      (Nat.perm_primeFactorsList_mul hm0 htail0)
  exact hperm.eq_of_sortedLE
    (Nat.primeFactorsList_sorted _) hsorted

/-- The last 1000 prime factors of the cofactor are exactly the selected tail
factors, independently of the chosen scale tuple. -/
theorem take_top_primeFactorsList_taoPrimeTupleEnlargedCofactor
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {x : ℕ} {a : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x) :
    (taoPrimeTupleTailProduct a.2 * a.1).primeFactorsList.reverse.take 1000 =
      (taoPrimeTupleTailProduct a.2).primeFactorsList.reverse := by
  rw [primeFactorsList_taoPrimeTupleEnlargedCofactor_eq hPmono hlast ha,
    List.reverse_append]
  have hlen := length_primeFactorsList_taoPrimeTupleTailProduct
    (mem_taoPrimeTupleEnlargedRemainderPairs.mp ha).2
  simp [hlen]

/-- Equal enlarged values, even at different ordered scales, have the same
tail product. -/
theorem taoPrimeTupleEnlarged_tailProduct_eq_of_value_eq
    {P Q : Fin 1001 → ℕ} (hPmono : Antitone P) (hQmono : Antitone Q)
    (hPlast : 2 ≤ P (Fin.last 1000))
    (hQlast : 2 ≤ Q (Fin.last 1000))
    {x : ℕ} {a b : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x)
    (hb : b ∈ taoPrimeTupleEnlargedRemainderPairs Q x)
    (hab : taoPrimeTupleEnlargedRemainderValue a =
      taoPrimeTupleEnlargedRemainderValue b) :
    taoPrimeTupleTailProduct a.2 = taoPrimeTupleTailProduct b.2 := by
  have hzero : a.2 0 = b.2 0 := by
    apply Option.some.inj
    exact (largestPrimeFactor_taoPrimeTupleEnlargedRemainderValue
        hPmono hPlast ha).symm.trans
      ((congrArg largestPrimeFactor hab).trans
        (largestPrimeFactor_taoPrimeTupleEnlargedRemainderValue
          hQmono hQlast hb))
  have hcofactor : taoPrimeTupleTailProduct a.2 * a.1 =
      taoPrimeTupleTailProduct b.2 * b.1 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos
      (mem_taoDyadicPrimeBand.mp
        ((mem_taoPrimeTupleEnlargedSupport.mp
          (mem_taoPrimeTupleEnlargedRemainderPairs.mp ha).2) 0)).1.pos 2)
    change (a.2 0) ^ 2 * taoPrimeTupleTailProduct a.2 * a.1 =
      (b.2 0) ^ 2 * taoPrimeTupleTailProduct b.2 * b.1 at hab
    rw [← hzero] at hab
    simpa only [Nat.mul_assoc] using hab
  have htop := congrArg (fun n : ℕ => n.primeFactorsList.reverse.take 1000)
    hcofactor
  have htopA := take_top_primeFactorsList_taoPrimeTupleEnlargedCofactor
    hPmono hPlast ha
  have htopB := take_top_primeFactorsList_taoPrimeTupleEnlargedCofactor
    hQmono hQlast hb
  have hfactors : (taoPrimeTupleTailProduct a.2).primeFactorsList =
      (taoPrimeTupleTailProduct b.2).primeFactorsList :=
    List.reverse_injective (htopA.symm.trans (htop.trans htopB))
  have htailA0 : taoPrimeTupleTailProduct a.2 ≠ 0 := by
    unfold taoPrimeTupleTailProduct
    exact Finset.prod_ne_zero_iff.mpr fun j hj =>
      (mem_taoDyadicPrimeBand.mp
        ((mem_taoPrimeTupleEnlargedSupport.mp
          (mem_taoPrimeTupleEnlargedRemainderPairs.mp ha).2) j)).1.ne_zero
  have htailB0 : taoPrimeTupleTailProduct b.2 ≠ 0 := by
    unfold taoPrimeTupleTailProduct
    exact Finset.prod_ne_zero_iff.mpr fun j hj =>
      (mem_taoDyadicPrimeBand.mp
        ((mem_taoPrimeTupleEnlargedSupport.mp
          (mem_taoPrimeTupleEnlargedRemainderPairs.mp hb).2) j)).1.ne_zero
  rw [← Nat.prod_primeFactorsList htailA0, hfactors,
    Nat.prod_primeFactorsList htailB0]

/-- A prime in two dyadic bands with power-of-two lower endpoints determines
the exponent uniquely, even after multiplication by a fixed positive factor. -/
theorem eq_of_mem_taoDyadicPrimeBand_mul_two_pow
    {c r s p : ℕ}
    (hr : p ∈ taoDyadicPrimeBand (c * 2 ^ r))
    (hs : p ∈ taoDyadicPrimeBand (c * 2 ^ s)) : r = s := by
  have hrData := mem_taoDyadicPrimeBand.mp hr
  have hsData := mem_taoDyadicPrimeBand.mp hs
  apply le_antisymm
  · by_contra hrs
    have hsr : s + 1 ≤ r := by omega
    have hpow : 2 ^ (s + 1) ≤ 2 ^ r :=
      Nat.pow_le_pow_right (by norm_num) hsr
    have : c * 2 ^ r < c * 2 ^ r := by
      calc
        c * 2 ^ r ≤ p := hrData.2.1
        _ < 2 * (c * 2 ^ s) := hsData.2.2
        _ = c * 2 ^ (s + 1) := by rw [pow_succ]; ring
        _ ≤ c * 2 ^ r := Nat.mul_le_mul_left c hpow
    omega
  · by_contra hsr
    have hrs : r + 1 ≤ s := by omega
    have hpow : 2 ^ (r + 1) ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) hrs
    have : c * 2 ^ s < c * 2 ^ s := by
      calc
        c * 2 ^ s ≤ p := hsData.2.1
        _ < 2 * (c * 2 ^ r) := hrData.2.2
        _ = c * 2 ^ (r + 1) := by rw [pow_succ]; ring
        _ ≤ c * 2 ^ s := Nat.mul_le_mul_left c hpow
    omega

/-- Equal supported prime tuples recover equal scale exponent tuples. -/
theorem taoPrimeTupleSlowScaleExponentTuple_eq_of_enlargedTuple_eq
    {R S : Fin 1001 → ℕ} {ω η : TaoPrimeTuple}
    (hω : ω ∈ taoPrimeTupleEnlargedSupport (taoPrimeTupleDyadicScales R))
    (hη : η ∈ taoPrimeTupleEnlargedSupport (taoPrimeTupleDyadicScales S))
    (hEq : ω = η) : R = S := by
  subst η
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
  · apply eq_of_mem_taoDyadicPrimeBand_mul_two_pow
    · simpa [taoPrimeTupleEnlargedScale, taoPrimeTupleDyadicScales] using
        (mem_taoPrimeTupleEnlargedSupport.mp hω 0)
    · simpa [taoPrimeTupleEnlargedScale, taoPrimeTupleDyadicScales] using
        (mem_taoPrimeTupleEnlargedSupport.mp hη 0)
  · apply eq_of_mem_taoDyadicPrimeBand_mul_two_pow
    · simpa [taoPrimeTupleEnlargedScale, taoPrimeTupleDyadicScales] using
        (mem_taoPrimeTupleEnlargedSupport.mp hω i.succ)
    · simpa [taoPrimeTupleEnlargedScale, taoPrimeTupleDyadicScales] using
        (mem_taoPrimeTupleEnlargedSupport.mp hη i.succ)

/-- One fiber of the global enlarged evaluation map. -/
def taoPrimeTupleGlobalEnlargedRemainderFiber
    (q : ℕ → ℕ) (x n : ℕ) :
    Finset (Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple) :=
  (taoPrimeTupleGlobalEnlargedRemainderPairs q x).filter fun b =>
    taoPrimeTupleGlobalEnlargedRemainderValue b = n

theorem mem_taoPrimeTupleGlobalEnlargedRemainderFiber
    {q : ℕ → ℕ} {x n : ℕ}
    {b : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple} :
    b ∈ taoPrimeTupleGlobalEnlargedRemainderFiber q x n ↔
      b ∈ taoPrimeTupleGlobalEnlargedRemainderPairs q x ∧
        taoPrimeTupleGlobalEnlargedRemainderValue b = n := by
  simp [taoPrimeTupleGlobalEnlargedRemainderFiber]

/-- The tail-coordinate code of a global representation. -/
def taoPrimeTupleGlobalTailCode
    (b : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple) : Fin 1000 → ℕ :=
  taoPrimeTupleTailCode b.2.2

/-- A global fiber still injects into the 1000-coordinate tail-code space. -/
theorem injOn_taoPrimeTupleTailCode_globalEnlargedFiber
    {q : ℕ → ℕ} {x : ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x)
    {a : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple} :
    Set.InjOn taoPrimeTupleGlobalTailCode
      (taoPrimeTupleGlobalEnlargedRemainderFiber q x
        (taoPrimeTupleGlobalEnlargedRemainderValue a)) := by
  rintro ⟨R, m, ω⟩ hb ⟨S, m', η⟩ hb' hcode
  have hbData := mem_taoPrimeTupleGlobalEnlargedRemainderFiber.mp hb
  have hbData' := mem_taoPrimeTupleGlobalEnlargedRemainderFiber.mp hb'
  have hRData := mem_taoPrimeTupleGlobalEnlargedRemainderPairs.mp hbData.1
  have hSData := mem_taoPrimeTupleGlobalEnlargedRemainderPairs.mp hbData'.1
  have hRGrid := mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hRData.1
  have hSGrid := mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hSData.1
  have hPmono := antitone_taoPrimeTupleDyadicScales hRGrid.2
  have hQmono := antitone_taoPrimeTupleDyadicScales hSGrid.2
  have hPlast := two_le_taoPrimeTupleDyadicScales_last_of_mem hlower
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr hRGrid.1)
  have hQlast := two_le_taoPrimeTupleDyadicScales_last_of_mem hlower
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr hSGrid.1)
  have hvalue : taoPrimeTupleEnlargedRemainderValue ⟨m, ω⟩ =
      taoPrimeTupleEnlargedRemainderValue ⟨m', η⟩ :=
    hbData.2.trans hbData'.2.symm
  have hzero : ω 0 = η 0 := by
    apply Option.some.inj
    exact (largestPrimeFactor_taoPrimeTupleEnlargedRemainderValue
        hPmono hPlast hRData.2).symm.trans
      ((congrArg largestPrimeFactor hvalue).trans
        (largestPrimeFactor_taoPrimeTupleEnlargedRemainderValue
          hQmono hQlast hSData.2))
  have hω : ω = η := by
    funext j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · exact hzero
    · exact congrFun hcode i
  have hRS : R = S :=
    taoPrimeTupleSlowScaleExponentTuple_eq_of_enlargedTuple_eq
      (mem_taoPrimeTupleEnlargedRemainderPairs.mp hRData.2).2
      (mem_taoPrimeTupleEnlargedRemainderPairs.mp hSData.2).2 hω
  subst S
  subst η
  have hsupport := mem_taoPrimeTupleEnlargedSupport.mp
    (mem_taoPrimeTupleEnlargedRemainderPairs.mp hRData.2).2
  have hp := mem_taoDyadicPrimeBand.mp (hsupport 0) |>.1
  have htailPos : 0 < taoPrimeTupleTailProduct ω := by
    unfold taoPrimeTupleTailProduct
    exact Finset.prod_pos fun j hj =>
      (mem_taoDyadicPrimeBand.mp (hsupport j)).1.pos
  have hcoefficient : 0 < (ω 0) ^ 2 * taoPrimeTupleTailProduct ω :=
    Nat.mul_pos (pow_pos hp.pos 2) htailPos
  have hm : m = m' := by
    apply Nat.eq_of_mul_eq_mul_left hcoefficient
    exact hvalue
  subst m'
  rfl

/-- Each tail coordinate in a global value fiber uses the reference tail
alphabet. -/
theorem taoPrimeTupleGlobalEnlarged_tail_mem_reference
    {q : ℕ → ℕ} {x : ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x)
    {a b : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleGlobalEnlargedRemainderPairs q x)
    (hb : b ∈ taoPrimeTupleGlobalEnlargedRemainderPairs q x)
    (hba : taoPrimeTupleGlobalEnlargedRemainderValue b =
      taoPrimeTupleGlobalEnlargedRemainderValue a)
    (i : Fin 1000) :
    b.2.2 i.succ ∈ taoPrimeTupleTailCoordinateValues a.2.2 := by
  have haData := mem_taoPrimeTupleGlobalEnlargedRemainderPairs.mp ha
  have hbData := mem_taoPrimeTupleGlobalEnlargedRemainderPairs.mp hb
  have hRData := mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp haData.1
  have hSData := mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hbData.1
  have hPmono := antitone_taoPrimeTupleDyadicScales hRData.2
  have hQmono := antitone_taoPrimeTupleDyadicScales hSData.2
  have hPlast := two_le_taoPrimeTupleDyadicScales_last_of_mem hlower
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr hRData.1)
  have hQlast := two_le_taoPrimeTupleDyadicScales_last_of_mem hlower
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr hSData.1)
  have htailEq := taoPrimeTupleEnlarged_tailProduct_eq_of_value_eq
    hQmono hPmono hQlast hPlast hbData.2 haData.2 hba
  have hq := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp
      (mem_taoPrimeTupleEnlargedRemainderPairs.mp hbData.2).2) i.succ) |>.1
  have hiMem : i.succ ∈ (Finset.univ.erase (0 : Fin 1001)) := by simp
  have hqTailB : b.2.2 i.succ ∣ taoPrimeTupleTailProduct b.2.2 := by
    unfold taoPrimeTupleTailProduct
    exact Finset.dvd_prod_of_mem b.2.2 hiMem
  have hqTailA : b.2.2 i.succ ∣ taoPrimeTupleTailProduct a.2.2 := by
    rw [← htailEq]
    exact hqTailB
  unfold taoPrimeTupleTailProduct at hqTailA
  obtain ⟨j, hj, hqj⟩ :=
    (Prime.dvd_finsetProd_iff hq.prime a.2.2).mp hqTailA
  have hajPrime := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp
      (mem_taoPrimeTupleEnlargedRemainderPairs.mp haData.2).2) j) |>.1
  have hEq : b.2.2 i.succ = a.2.2 j :=
    (Nat.prime_dvd_prime_iff_eq hq hajPrime).mp hqj
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
  · simp at hj
  · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hEq.symm⟩

/-- Tail-code embedding from one global fiber into the reference code space. -/
def taoPrimeTupleGlobalTailCodeEmbedding
    {q : ℕ → ℕ} {x : ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x)
    {a : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleGlobalEnlargedRemainderPairs q x) :
    ↥(taoPrimeTupleGlobalEnlargedRemainderFiber q x
        (taoPrimeTupleGlobalEnlargedRemainderValue a)) →
      ↥(taoPrimeTupleTailCodeSpace a.2.2) := by
  classical
  intro b
  refine ⟨taoPrimeTupleTailCode b.1.2.2, ?_⟩
  rw [mem_taoPrimeTupleTailCodeSpace]
  intro i
  have hbData := mem_taoPrimeTupleGlobalEnlargedRemainderFiber.mp b.2
  exact taoPrimeTupleGlobalEnlarged_tail_mem_reference
    (q := q) (x := x) (a := a) (b := b.1)
      hlower ha hbData.1 hbData.2 i

theorem taoPrimeTupleGlobalTailCodeEmbedding_injective
    {q : ℕ → ℕ} {x : ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x)
    {a : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleGlobalEnlargedRemainderPairs q x) :
    Function.Injective
      (taoPrimeTupleGlobalTailCodeEmbedding hlower ha) := by
  intro b c hbc
  apply Subtype.ext
  apply injOn_taoPrimeTupleTailCode_globalEnlargedFiber
    (q := q) (x := x) hlower b.2 c.2
  have hvalues := congrArg Subtype.val hbc
  simpa only [taoPrimeTupleGlobalTailCodeEmbedding,
    taoPrimeTupleGlobalTailCode] using hvalues

/-- Global enlarged fibers retain the absolute `1000 ^ 1000` bound. -/
theorem card_taoPrimeTupleGlobalEnlargedRemainderValue_fiber_le
    {q : ℕ → ℕ} {x : ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x)
    {a : Σ _R : (Fin 1001 → ℕ), Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleGlobalEnlargedRemainderPairs q x) :
    (taoPrimeTupleGlobalEnlargedRemainderFiber q x
      (taoPrimeTupleGlobalEnlargedRemainderValue a)).card ≤ 1000 ^ 1000 := by
  calc
    (taoPrimeTupleGlobalEnlargedRemainderFiber q x
        (taoPrimeTupleGlobalEnlargedRemainderValue a)).card =
        Fintype.card ↥(taoPrimeTupleGlobalEnlargedRemainderFiber q x
          (taoPrimeTupleGlobalEnlargedRemainderValue a)) := by
      rw [Fintype.card_coe]
    _ ≤ Fintype.card ↥(taoPrimeTupleTailCodeSpace a.2.2) :=
      Fintype.card_le_of_injective
        (taoPrimeTupleGlobalTailCodeEmbedding hlower ha)
        (taoPrimeTupleGlobalTailCodeEmbedding_injective hlower ha)
    _ = (taoPrimeTupleTailCodeSpace a.2.2).card := Fintype.card_coe _
    _ ≤ 1000 ^ 1000 := card_taoPrimeTupleTailCodeSpace_le a.2.2

/-- The global enlarged image lies in the literal one-term set at the same
fixed absolute dilation. -/
theorem image_taoPrimeTupleGlobalEnlargedRemainderPairs_subset_badOneTermNumbersUpTo
    {q : ℕ → ℕ} {x : ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x) :
    (taoPrimeTupleGlobalEnlargedRemainderPairs q x).image
        taoPrimeTupleGlobalEnlargedRemainderValue ⊆
      badOneTermNumbersUpTo (2 * taoPrimeTupleEnlargementFactor * x) := by
  intro n hn
  rw [Finset.mem_image] at hn
  obtain ⟨a, ha, rfl⟩ := hn
  have haData := mem_taoPrimeTupleGlobalEnlargedRemainderPairs.mp ha
  have hRData := mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp haData.1
  exact image_taoPrimeTupleEnlargedRemainderPairs_subset_badOneTermNumbersUpTo
    (antitone_taoPrimeTupleDyadicScales hRData.2)
    (two_le_taoPrimeTupleDyadicScales_last_of_mem hlower
      (mem_taoPrimeTupleSlowScaleExponentTuples.mpr hRData.1)) x
    (Finset.mem_image_of_mem taoPrimeTupleEnlargedRemainderValue haData.2)

/-- The entire enlarged family over all ordered scales is controlled by one
literal bad-set count and one absolute multiplicity constant. -/
theorem card_taoPrimeTupleGlobalEnlargedRemainderPairs_le_badOneTermCount_mul
    {q : ℕ → ℕ} {x : ℕ}
    (hlower : 2 ≤ taoPrimeTupleSlowLowerCutoff q x) :
    (taoPrimeTupleGlobalEnlargedRemainderPairs q x).card ≤
      badOneTermCount (2 * taoPrimeTupleEnlargementFactor * x) *
        (1000 ^ 1000) := by
  refine (card_le_card_image_mul_of_fiber_card_le
    (taoPrimeTupleGlobalEnlargedRemainderPairs q x)
    taoPrimeTupleGlobalEnlargedRemainderValue (1000 ^ 1000) ?_).trans ?_
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact card_taoPrimeTupleGlobalEnlargedRemainderValue_fiber_le hlower ha
  · apply Nat.mul_le_mul_right
    change ((taoPrimeTupleGlobalEnlargedRemainderPairs q x).image
        taoPrimeTupleGlobalEnlargedRemainderValue).card ≤
      (badOneTermNumbersUpTo (2 * taoPrimeTupleEnlargementFactor * x)).card
    exact Finset.card_le_card
      (image_taoPrimeTupleGlobalEnlargedRemainderPairs_subset_badOneTermNumbersUpTo
        hlower)

end

end Tao2026

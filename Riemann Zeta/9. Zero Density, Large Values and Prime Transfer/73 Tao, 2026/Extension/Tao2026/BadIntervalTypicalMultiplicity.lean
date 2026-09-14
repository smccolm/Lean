import Tao2026.BadIntervalTypicalEnlargement

/-!
# Bounded multiplicity of the enlarged typical representations

For fixed ordered dyadic scales, the distinguished prime is recovered as the
largest prime factor of the represented integer.  Every selected tail prime
is larger than the smoothness cutoff, so equality of represented integers
forces it to occur among the 1000 tail primes of any fixed reference
representation.  Encoding the tail coordinates consequently gives the
absolute fiber bound `1000 ^ 1000`.
-/

namespace Tao2026

open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 8000

/-- The 1000 coordinates after the distinguished zeroth coordinate. -/
def taoPrimeTupleTailCode (ω : TaoPrimeTuple) : Fin 1000 → ℕ :=
  fun i => ω i.succ

/-- The distinct values occurring among the tail coordinates. -/
def taoPrimeTupleTailCoordinateValues (ω : TaoPrimeTuple) : Finset ℕ :=
  (Finset.univ : Finset (Fin 1000)).image (taoPrimeTupleTailCode ω)

/-- All length-1000 words in the tail-coordinate alphabet of `ω`. -/
def taoPrimeTupleTailCodeSpace (ω : TaoPrimeTuple) :
    Finset (Fin 1000 → ℕ) :=
  Fintype.piFinset fun _ => taoPrimeTupleTailCoordinateValues ω

theorem mem_taoPrimeTupleTailCodeSpace {ω η : TaoPrimeTuple} :
    taoPrimeTupleTailCode η ∈ taoPrimeTupleTailCodeSpace ω ↔
      ∀ i : Fin 1000, η i.succ ∈ taoPrimeTupleTailCoordinateValues ω := by
  simp [taoPrimeTupleTailCodeSpace, taoPrimeTupleTailCode]

theorem card_taoPrimeTupleTailCoordinateValues_le (ω : TaoPrimeTuple) :
    (taoPrimeTupleTailCoordinateValues ω).card ≤ 1000 := by
  unfold taoPrimeTupleTailCoordinateValues
  simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 1000)))
    (f := taoPrimeTupleTailCode ω)

theorem card_taoPrimeTupleTailCodeSpace_le (ω : TaoPrimeTuple) :
    (taoPrimeTupleTailCodeSpace ω).card ≤ 1000 ^ 1000 := by
  rw [taoPrimeTupleTailCodeSpace, Fintype.card_piFinset]
  calc
    ∏ _i : Fin 1000, (taoPrimeTupleTailCoordinateValues ω).card ≤
        ∏ _i : Fin 1000, 1000 := by
      exact Finset.prod_le_prod' fun _ _ =>
        card_taoPrimeTupleTailCoordinateValues_le ω
    _ = 1000 ^ 1000 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Every enlarged tail prime is strictly above the smoothness cutoff. -/
theorem taoPrimeTupleRemainderSmoothnessCutoff_lt_enlarged_tail
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {ω : TaoPrimeTuple} (hω : ω ∈ taoPrimeTupleEnlargedSupport P)
    {j : Fin 1001} (hj : j ≠ 0) :
    taoPrimeTupleRemainderSmoothnessCutoff P < ω j := by
  have hjData := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp hω) j)
  rw [taoPrimeTupleEnlargedScale_of_ne_zero P hj] at hjData
  have hPj : 2 ≤ P j := hlast.trans (hPmono (Fin.le_last j))
  have hcutLe : taoPrimeTupleRemainderSmoothnessCutoff P ≤ ω j := by
    unfold taoPrimeTupleRemainderSmoothnessCutoff
    exact (Nat.mul_le_mul_left 2 (hPmono (Fin.le_last j))).trans hjData.2.1
  apply hcutLe.lt_of_ne
  intro heq
  have htwoDvd : 2 ∣ ω j := by
    rw [← heq]
    unfold taoPrimeTupleRemainderSmoothnessCutoff
    exact dvd_mul_right 2 (P (Fin.last 1000))
  have htwoEq : 2 = ω j :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_two hjData.1).mp htwoDvd
  omega

/-- The distinguished coordinate is the largest prime factor of every
enlarged represented value. -/
theorem largestPrimeFactor_taoPrimeTupleEnlargedRemainderValue
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {x : ℕ} {a : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x) :
    largestPrimeFactor (taoPrimeTupleEnlargedRemainderValue a) =
      some (a.2 0) := by
  have haData := mem_taoPrimeTupleEnlargedRemainderPairs.mp ha
  have hp := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp haData.2) 0) |>.1
  have hcofactor := isSmooth_taoPrimeTupleEnlargedCofactor
    hPmono hlast ha
  have hsmooth :
      IsSmooth (a.2 0 * (taoPrimeTupleTailProduct a.2 * a.1)) (a.2 0) := by
    rw [isSmooth_iff]
    constructor
    · exact mul_ne_zero hp.ne_zero (isSmooth_iff.mp hcofactor).1
    · intro q hq hqdiv
      rcases hq.dvd_mul.mp hqdiv with hqp | hqc
      · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).le
      · exact (isSmooth_iff.mp hcofactor).2 q hq hqc
  simpa only [taoPrimeTupleEnlargedRemainderValue, taoPrimeTupleStart,
      pow_two, Nat.mul_assoc] using
    largestPrimeFactor_smoothLargestPrimeRepresentation hp hsmooth

/-- Equal enlarged values at the same ordered scales have equal distinguished
prime coordinates. -/
theorem taoPrimeTupleEnlarged_zero_eq_of_value_eq
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {x : ℕ} {a b : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x)
    (hb : b ∈ taoPrimeTupleEnlargedRemainderPairs P x)
    (hab : taoPrimeTupleEnlargedRemainderValue a =
      taoPrimeTupleEnlargedRemainderValue b) :
    a.2 0 = b.2 0 := by
  apply Option.some.inj
  exact (largestPrimeFactor_taoPrimeTupleEnlargedRemainderValue
      hPmono hlast ha).symm.trans
    ((congrArg largestPrimeFactor hab).trans
      (largestPrimeFactor_taoPrimeTupleEnlargedRemainderValue
        hPmono hlast hb))

/-- A tail prime in one representation occurs among the reference tail
coordinates of any equal representation. -/
theorem taoPrimeTupleEnlarged_tail_mem_reference_of_value_eq
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {x : ℕ} {a b : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x)
    (hb : b ∈ taoPrimeTupleEnlargedRemainderPairs P x)
    (hba : taoPrimeTupleEnlargedRemainderValue b =
      taoPrimeTupleEnlargedRemainderValue a) (i : Fin 1000) :
    b.2 i.succ ∈ taoPrimeTupleTailCoordinateValues a.2 := by
  have haData := mem_taoPrimeTupleEnlargedRemainderPairs.mp ha
  have hbData := mem_taoPrimeTupleEnlargedRemainderPairs.mp hb
  have hzero : b.2 0 = a.2 0 :=
    taoPrimeTupleEnlarged_zero_eq_of_value_eq hPmono hlast hb ha hba
  have hq := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp hbData.2) i.succ) |>.1
  have hqAbove : taoPrimeTupleRemainderSmoothnessCutoff P < b.2 i.succ :=
    taoPrimeTupleRemainderSmoothnessCutoff_lt_enlarged_tail
      hPmono hlast hbData.2 (by simp)
  have hiMem : i.succ ∈ (Finset.univ.erase (0 : Fin 1001)) := by simp
  have hqTailB : b.2 i.succ ∣ taoPrimeTupleTailProduct b.2 := by
    unfold taoPrimeTupleTailProduct
    exact Finset.dvd_prod_of_mem b.2 hiMem
  have hqValueB : b.2 i.succ ∣ taoPrimeTupleEnlargedRemainderValue b := by
    unfold taoPrimeTupleEnlargedRemainderValue taoPrimeTupleStart
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqTailB _) _
  have hqValueA : b.2 i.succ ∣ taoPrimeTupleEnlargedRemainderValue a := by
    rw [← hba]
    exact hqValueB
  unfold taoPrimeTupleEnlargedRemainderValue taoPrimeTupleStart at hqValueA
  rcases hq.dvd_mul.mp hqValueA with hqPrefix | hqm
  · rcases hq.dvd_mul.mp hqPrefix with hqZeroSq | hqTailA
    · have hqZero : b.2 i.succ ∣ a.2 0 := hq.dvd_of_dvd_pow hqZeroSq
      have haZeroPrime := mem_taoDyadicPrimeBand.mp
        ((mem_taoPrimeTupleEnlargedSupport.mp haData.2) 0) |>.1
      have hEq : b.2 i.succ = a.2 0 :=
        (Nat.prime_dvd_prime_iff_eq hq haZeroPrime).mp hqZero
      have hltZero := taoPrimeTupleEnlarged_tail_lt_zero
        hPmono hbData.2 (by simp : i.succ ≠ (0 : Fin 1001))
      omega
    · unfold taoPrimeTupleTailProduct at hqTailA
      obtain ⟨j, hj, hqj⟩ :=
        (Prime.dvd_finsetProd_iff hq.prime a.2).mp hqTailA
      have hajPrime := mem_taoDyadicPrimeBand.mp
        ((mem_taoPrimeTupleEnlargedSupport.mp haData.2) j) |>.1
      have hEq : b.2 i.succ = a.2 j :=
        (Nat.prime_dvd_prime_iff_eq hq hajPrime).mp hqj
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · simp at hj
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hEq.symm⟩
  · have hmSmooth := (mem_taoPrimeTupleSmoothRemainders.mp haData.1).2
    have hqLe := (isSmooth_iff.mp hmSmooth).2 (b.2 i.succ) hq hqm
    omega

/-- On one value fiber, the tail code is injective. -/
theorem injOn_taoPrimeTupleTailCode_enlargedFiber
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000)) (x : ℕ)
    {a : Σ _m' : ℕ, TaoPrimeTuple} :
    Set.InjOn (fun b : Σ _m' : ℕ, TaoPrimeTuple =>
        taoPrimeTupleTailCode b.2)
      ((taoPrimeTupleEnlargedRemainderPairs P x).filter fun b =>
        taoPrimeTupleEnlargedRemainderValue b =
          taoPrimeTupleEnlargedRemainderValue a) := by
  rintro ⟨m, ω⟩ hb ⟨m', ω'⟩ hb' hcode
  have hbData := Finset.mem_filter.mp hb
  have hbData' := Finset.mem_filter.mp hb'
  have hvalue : taoPrimeTupleEnlargedRemainderValue ⟨m, ω⟩ =
      taoPrimeTupleEnlargedRemainderValue ⟨m', ω'⟩ :=
    hbData.2.trans hbData'.2.symm
  have hzero : ω 0 = ω' 0 := taoPrimeTupleEnlarged_zero_eq_of_value_eq
    hPmono hlast hbData.1 hbData'.1 hvalue
  have hω : ω = ω' := by
    funext j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · exact hzero
    · exact congrFun hcode i
  subst ω'
  have hsupport := mem_taoPrimeTupleEnlargedSupport.mp
    (mem_taoPrimeTupleEnlargedRemainderPairs.mp hbData.1).2
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

/-- Each fiber of the enlarged representation map at fixed ordered scales has
absolute cardinality at most `1000 ^ 1000`. -/
theorem card_taoPrimeTupleEnlargedRemainderValue_fiber_le
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000)) (x : ℕ)
    {a : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x) :
    ((taoPrimeTupleEnlargedRemainderPairs P x).filter fun b =>
        taoPrimeTupleEnlargedRemainderValue b =
          taoPrimeTupleEnlargedRemainderValue a).card ≤ 1000 ^ 1000 := by
  refine (Finset.card_le_card_of_injOn
    (fun b : Σ _m' : ℕ, TaoPrimeTuple => taoPrimeTupleTailCode b.2)
    ?_ (injOn_taoPrimeTupleTailCode_enlargedFiber hPmono hlast x)).trans
    (card_taoPrimeTupleTailCodeSpace_le a.2)
  intro b hb
  change taoPrimeTupleTailCode b.2 ∈ taoPrimeTupleTailCodeSpace a.2
  rw [mem_taoPrimeTupleTailCodeSpace]
  intro i
  have hbData := Finset.mem_filter.mp hb
  exact taoPrimeTupleEnlarged_tail_mem_reference_of_value_eq
    hPmono hlast ha hbData.1 hbData.2 i

/-- A finite map whose fibers have cardinality at most `M` loses at most the
factor `M` when passed to its image. -/
theorem card_le_card_image_mul_of_fiber_card_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (M : ℕ)
    (hfiber : ∀ y ∈ s.image f, (s.filter fun a => f a = y).card ≤ M) :
    s.card ≤ (s.image f).card * M := by
  rw [Finset.card_eq_sum_card_image f s]
  calc
    ∑ y ∈ s.image f, (s.filter fun a => f a = y).card ≤
        ∑ _y ∈ s.image f, M := Finset.sum_le_sum fun y hy => hfiber y hy
    _ = (s.image f).card * M := by simp

/-- Fixed-scale enlarged source cardinality is controlled by the literal
one-term bad count, with one absolute multiplicity constant. -/
theorem card_taoPrimeTupleEnlargedRemainderPairs_le_badOneTermCount_mul
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000)) (x : ℕ) :
    (taoPrimeTupleEnlargedRemainderPairs P x).card ≤
      badOneTermCount (2 * taoPrimeTupleEnlargementFactor * x) *
        (1000 ^ 1000) := by
  refine (card_le_card_image_mul_of_fiber_card_le
    (taoPrimeTupleEnlargedRemainderPairs P x)
    taoPrimeTupleEnlargedRemainderValue (1000 ^ 1000) ?_).trans ?_
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact card_taoPrimeTupleEnlargedRemainderValue_fiber_le
      hPmono hlast x ha
  · exact Nat.mul_le_mul_right (1000 ^ 1000)
      (card_image_taoPrimeTupleEnlargedRemainderPairs_le_badOneTermCount
        hPmono hlast x)

end

end Tao2026

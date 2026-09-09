import Tao2026.QuadraticUnits

/-!
# Ideal-divisor exponent vectors for Tao's Lemma 2.10

Divisors of a nonzero ideal in a ring of integers are encoded injectively by
their prime-ideal multiplicities.  Unlike the raw powerset construction used
merely to obtain finiteness, this gives the exact Euler-factor-shaped upper
bound `∏ P, (v_P(J)+1)`.  It is the correct intermediate statement for the
source's comparison with `d(|N|)^2` in a quadratic field.
-/

namespace Tao2026

open scoped NumberField
open UniqueFactorizationMonoid

/-- The multiplicity vector of an ideal divisor, indexed only by the prime
ideal support of the ambient nonzero ideal. -/
noncomputable def idealDivisorExponentVector
    {K : Type*} [Field K] [NumberField K]
    (J : Ideal (𝓞 K)) (hJ : J ≠ 0)
    (I : {I : Ideal (𝓞 K) // I ∣ J}) :
    (P : {P : Ideal (𝓞 K) // P ∈ (normalizedFactors J).toFinset}) →
      Fin ((normalizedFactors J).count P.1 + 1) := by
  classical
  intro P
  have hI : I.1 ≠ 0 := by
    intro hzero
    apply hJ
    rw [← zero_dvd_iff]
    simpa [hzero] using I.2
  refine ⟨(normalizedFactors I.1).count P.1, ?_⟩
  have hle : normalizedFactors I.1 ≤ normalizedFactors J :=
    (dvd_iff_normalizedFactors_le_normalizedFactors hI hJ).mp I.2
  exact Nat.lt_succ_of_le (Multiset.count_le_of_le P.1 hle)

/-- Unique factorization and the fact that ideals have a unique unit make
the exponent-vector encoding injective. -/
theorem idealDivisorExponentVector_injective
    {K : Type*} [Field K] [NumberField K]
    (J : Ideal (𝓞 K)) (hJ : J ≠ 0) :
    Function.Injective (idealDivisorExponentVector J hJ) := by
  classical
  intro I L hvec
  apply Subtype.ext
  have hI : I.1 ≠ 0 := by
    intro hzero
    apply hJ
    rw [← zero_dvd_iff]
    simpa [hzero] using I.2
  have hL : L.1 ≠ 0 := by
    intro hzero
    apply hJ
    rw [← zero_dvd_iff]
    simpa [hzero] using L.2
  have hfac : normalizedFactors I.1 = normalizedFactors L.1 := by
    apply Multiset.ext.mpr
    intro P
    by_cases hPJ : P ∈ normalizedFactors J
    · let pJ : {P : Ideal (𝓞 K) //
          P ∈ (normalizedFactors J).toFinset} := ⟨P, by simpa using hPJ⟩
      have hp := congrFun hvec pJ
      exact congrArg Fin.val hp
    · have hleI : normalizedFactors I.1 ≤ normalizedFactors J :=
        (dvd_iff_normalizedFactors_le_normalizedFactors hI hJ).mp I.2
      have hleL : normalizedFactors L.1 ≤ normalizedFactors J :=
        (dvd_iff_normalizedFactors_le_normalizedFactors hL hJ).mp L.2
      have hzJ : (normalizedFactors J).count P = 0 :=
        Multiset.count_eq_zero.mpr hPJ
      have hzI : (normalizedFactors I.1).count P = 0 := by
        have := Multiset.count_le_of_le P hleI
        omega
      have hzL : (normalizedFactors L.1).count P = 0 := by
        have := Multiset.count_le_of_le P hleL
        omega
      rw [hzI, hzL]
  have hassoc : Associated I.1 L.1 :=
    (associated_iff_normalizedFactors_eq_normalizedFactors hI hL).mpr hfac
  exact associated_iff_eq.mp hassoc

/-- Exact multiplicity-product upper bound for the number of ideal divisors
of a nonzero ideal in a number field. -/
theorem card_ideal_divisors_le_prod_normalizedFactors
    {K : Type*} [Field K] [NumberField K]
    (J : Ideal (𝓞 K)) (hJ : J ≠ 0) :
    Nat.card {I : Ideal (𝓞 K) // I ∣ J} ≤
      ∏ P ∈ (normalizedFactors J).toFinset,
        ((normalizedFactors J).count P + 1) := by
  classical
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ
  calc
    Nat.card {I : Ideal (𝓞 K) // I ∣ J} =
        Fintype.card {I : Ideal (𝓞 K) // I ∣ J} := Nat.card_eq_fintype_card
    _ ≤ Fintype.card ((P : {P : Ideal (𝓞 K) //
          P ∈ (normalizedFactors J).toFinset}) →
            Fin ((normalizedFactors J).count P.1 + 1)) :=
      Fintype.card_le_of_injective (idealDivisorExponentVector J hJ)
        (idealDivisorExponentVector_injective J hJ)
    _ = ∏ P ∈ (normalizedFactors J).toFinset,
        ((normalizedFactors J).count P + 1) := by
      simp only [Fintype.card_pi, Fintype.card_fin,
        Finset.univ_eq_attach]
      exact Finset.prod_attach (normalizedFactors J).toFinset
        (fun P : Ideal (𝓞 K) => (normalizedFactors J).count P + 1)

/-- Specialization of the exact exponent-product bound to the principal
ideal `(N)` in the concrete quadratic field. -/
theorem card_maximalOrderIdealDivisors_le_prod_normalizedFactors
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ) (hN : N ≠ 0) :
    (maximalOrderIdealDivisors D N hN).card ≤
      ∏ P ∈ (normalizedFactors
        (Ideal.span ({(N : 𝓞 (quadraticField D))} :
          Set (𝓞 (quadraticField D))))).toFinset,
        ((normalizedFactors
          (Ideal.span ({(N : 𝓞 (quadraticField D))} :
            Set (𝓞 (quadraticField D))))).count P + 1) := by
  let J : Ideal (𝓞 (quadraticField D)) :=
    Ideal.span ({(N : 𝓞 (quadraticField D))} :
      Set (𝓞 (quadraticField D)))
  have hJ : J ≠ 0 := by
    change Ideal.span ({(N : 𝓞 (quadraticField D))} :
      Set (𝓞 (quadraticField D))) ≠ 0
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Int.cast_ne_zero.mpr hN
  have hcard : (maximalOrderIdealDivisors D N hN).card =
      Nat.card {I : Ideal (𝓞 (quadraticField D)) // I ∣ J} := by
    classical
    rw [maximalOrderIdealDivisors]
    simp only [J]
    letI := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hcard]
  exact card_ideal_divisors_le_prod_normalizedFactors J hJ

/-- Mapping the principal ideal `(N)` from `ℤ` to the maximal order gives
the principal ideal generated by the image of `N`. -/
theorem map_span_int_to_quadraticMaximalOrder
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ) :
    (Ideal.span ({N} : Set ℤ)).map
        (algebraMap ℤ (𝓞 (quadraticField D))) =
      Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))) := by
  rw [Ideal.map_span]
  congr 1
  ext x
  simp

/-- The exponent of a prime ideal `P` in the maximal-order ideal `(N)` is
its ramification index times the exponent of the rational prime below it.
This is the multiplicity identity behind Tao's `d(|N|)^2` estimate. -/
theorem count_maximalOrder_normalizedFactors_eq_ramificationIdx_mul_count_under
    (D : ℕ) [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    {P : Ideal (𝓞 (quadraticField D))}
    (hPmem : P ∈ normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))) :
    (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).count P =
      Ideal.ramificationIdx
        ((⟨P, (Ideal.prime_iff_isPrime
          (ne_zero_of_mem_normalizedFactors hPmem)).mp
            (prime_of_normalized_factor P hPmem),
          ne_zero_of_mem_normalizedFactors hPmem⟩ :
            IsDedekindDomain.HeightOneSpectrum
              (𝓞 (quadraticField D))).under ℤ).asIdeal P *
      (normalizedFactors (Ideal.span ({N} : Set ℤ))).count
        ((⟨P, (Ideal.prime_iff_isPrime
          (ne_zero_of_mem_normalizedFactors hPmem)).mp
            (prime_of_normalized_factor P hPmem),
          ne_zero_of_mem_normalizedFactors hPmem⟩ :
            IsDedekindDomain.HeightOneSpectrum
              (𝓞 (quadraticField D))).under ℤ).asIdeal := by
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 (quadraticField D)) :=
    ⟨P, (Ideal.prime_iff_isPrime
      (ne_zero_of_mem_normalizedFactors hPmem)).mp
        (prime_of_normalized_factor P hPmem),
      ne_zero_of_mem_normalizedFactors hPmem⟩
  let v : IsDedekindDomain.HeightOneSpectrum ℤ := w.under ℤ
  let I : Ideal ℤ := Ideal.span ({N} : Set ℤ)
  have hI : I ≠ ⊥ := by
    simpa [I, Ideal.span_singleton_eq_bot] using hN
  letI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    hI (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
      (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible w.ne_bot
  have hmap : I.map (algebraMap ℤ (𝓞 (quadraticField D))) =
      Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))) := by
    simpa only [I] using map_span_int_to_quadraticMaximalOrder D N
  rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible (hmap ▸ (by
        simpa only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
          using Int.cast_ne_zero.mpr hN)),
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible hI, hmap] at hem
  simp only [normalize_eq, I] at hem
  exact_mod_cast hem

/-- In the quadratic maximal order, the exponent above a rational prime is
at most twice the exponent below it. -/
theorem count_maximalOrder_normalizedFactors_le_two_mul_count_under
    (D : ℕ) [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    {P : Ideal (𝓞 (quadraticField D))}
    (hPmem : P ∈ normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))) :
    (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).count P ≤
      2 * (normalizedFactors (Ideal.span ({N} : Set ℤ))).count
        ((⟨P, (Ideal.prime_iff_isPrime
          (ne_zero_of_mem_normalizedFactors hPmem)).mp
            (prime_of_normalized_factor P hPmem),
          ne_zero_of_mem_normalizedFactors hPmem⟩ :
            IsDedekindDomain.HeightOneSpectrum
              (𝓞 (quadraticField D))).under ℤ).asIdeal := by
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 (quadraticField D)) :=
    ⟨P, (Ideal.prime_iff_isPrime
      (ne_zero_of_mem_normalizedFactors hPmem)).mp
        (prime_of_normalized_factor P hPmem),
      ne_zero_of_mem_normalizedFactors hPmem⟩
  let v : IsDedekindDomain.HeightOneSpectrum ℤ := w.under ℤ
  letI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  letI : w.asIdeal.IsPrime := w.isPrime
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  haveI : IsScalarTower ℤ (𝓞 (quadraticField D)) (quadraticField D) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hscalar : IsScalarTower ℤ (𝓞 (quadraticField D))
      (quadraticField D) := inferInstance
  have hram : v.asIdeal.ramificationIdx w.asIdeal ≤ 2 := by
    simpa only [Algebra.IsQuadraticExtension.finrank_eq_two] using
      (@Ideal.ramificationIdx_le_finrank
        ℤ _ (𝓞 (quadraticField D)) _ _ _ ℚ (quadraticField D)
        _ _ _ _ _ _ _ _ _ hscalar _ _ _ v.asIdeal _ w.asIdeal _ _)
  rw [count_maximalOrder_normalizedFactors_eq_ramificationIdx_mul_count_under
    D hN hPmem]
  exact Nat.mul_le_mul_right _ hram

/-- The Euler factor product for the principal ideal `(N)` in `ℤ` is the
same product over the normalized integer prime factors of `N`. -/
theorem prod_intIdeal_normalizedFactors_eq_prod_int_normalizedFactors
    (N : ℤ) (hN : N ≠ 0) :
    ∏ I ∈ (normalizedFactors (Ideal.span ({N} : Set ℤ))).toFinset,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count I + 1) =
      ∏ d ∈ (normalizedFactors N).toFinset,
        ((normalizedFactors N).count d + 1) := by
  classical
  symm
  apply Finset.prod_bij (fun d _ ↦ Ideal.span ({d} : Set ℤ))
  · intro d hd
    exact Multiset.mem_toFinset.mpr
      (Ideal.singleton_span_mem_normalizedFactors_of_mem_normalizedFactors
        (Multiset.mem_toFinset.mp hd))
  · intro a ha b hb hab
    rw [Ideal.span_singleton_eq_span_singleton] at hab
    exact mem_normalizedFactors_eq_of_associated
      (Multiset.mem_toFinset.mp ha) (Multiset.mem_toFinset.mp hb) hab
  · intro I hI
    obtain ⟨⟨d, hd⟩, heq⟩ :=
      (Ideal.normalizedFactorsEquivSpanNormalizedFactors hN).surjective
        ⟨I, Multiset.mem_toFinset.mp hI⟩
    refine ⟨d, Multiset.mem_toFinset.mpr hd, ?_⟩
    exact congrArg Subtype.val heq
  · intro d hd
    have hp : Prime d := prime_of_normalized_factor d
      (Multiset.mem_toFinset.mp hd)
    simpa [normalize_normalized_factor d (Multiset.mem_toFinset.mp hd)] using
      (Ideal.count_span_normalizedFactors_eq hN hp).symm

/-- The normalized-factor Euler product of a nonzero integer is exactly its
ordinary positive-divisor count.  This includes the sign-normalization bridge
from `ℤ` to the factorization of `|N| : ℕ`. -/
theorem prod_int_normalizedFactors_eq_card_divisors
    (N : ℤ) (hN : N ≠ 0) :
    ∏ d ∈ (normalizedFactors N).toFinset,
        ((normalizedFactors N).count d + 1) = N.natAbs.divisors.card := by
  classical
  rw [Nat.card_divisors (Int.natAbs_ne_zero.mpr hN)]
  symm
  refine Finset.prod_bij
    (s := N.natAbs.primeFactors)
    (t := (normalizedFactors N).toFinset)
    (fun (p : ℕ) _ ↦ (p : ℤ)) ?_ ?_ ?_ ?_
  · intro p hp
    change (p : ℤ) ∈ (normalizedFactors N).toFinset
    apply Multiset.mem_toFinset.mpr
    apply UniqueFactorizationMonoid.mem_primeFactors.mp
    rw [UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs]
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩
  · intro p hp q hq hpq
    change (p : ℤ) = (q : ℤ) at hpq
    exact Int.ofNat_inj.mp hpq
  · intro d hd
    change ∃ a, ∃ (ha : a ∈ N.natAbs.primeFactors), (a : ℤ) = d
    have hdpf : d ∈ UniqueFactorizationMonoid.primeFactors N :=
      UniqueFactorizationMonoid.mem_primeFactors.mpr
        (Multiset.mem_toFinset.mp hd)
    rw [UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs] at hdpf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hdpf
    exact ⟨p, hp, rfl⟩
  · intro p hp
    change N.natAbs.factorization p + 1 =
      (normalizedFactors N).count (p : ℤ) + 1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hcountInt : (normalizedFactors N).count (p : ℤ) =
        (normalizedFactors N.natAbs).count p := by
      have h := Int.emultiplicity_natAbs p N
      rw [emultiplicity_eq_count_normalizedFactors
            (Nat.prime_iff.mp hpprime).irreducible
            (Int.natAbs_ne_zero.mpr hN),
        emultiplicity_eq_count_normalizedFactors
          ((Nat.prime_iff_prime_int.mp hpprime).irreducible) hN] at h
      simpa [Int.normalize_coe_nat] using h.symm
    have hcountNat : (normalizedFactors N.natAbs).count p =
        N.natAbs.factorization p := by
      rw [← factorization_eq_count]
      change Multiset.toFinsupp (normalizedFactors N.natAbs) p = _
      rw [Nat.factorization_eq_primeFactorsList_multiset, Nat.factors_eq]
    omega

/-- The Euler product for the rational principal ideal `(N)` is the ordinary
divisor function `d(|N|)`. -/
theorem prod_intIdeal_normalizedFactors_eq_card_divisors
    (N : ℤ) (hN : N ≠ 0) :
    ∏ I ∈ (normalizedFactors (Ideal.span ({N} : Set ℤ))).toFinset,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count I + 1) =
      N.natAbs.divisors.card := by
  rw [prod_intIdeal_normalizedFactors_eq_prod_int_normalizedFactors N hN,
    prod_int_normalizedFactors_eq_card_divisors N hN]

/-- In a quadratic maximal order, the sum of ramification indices over any
subfamily of the primes above a fixed nonzero rational prime is at most two.
This is the sharp degree-two input, obtained from the ramification-inertia
fundamental identity rather than from a coarse bound on each prime. -/
theorem sum_ramificationIdx_subset_le_two
    (D : ℕ) [Fact (¬ IsSquare D)]
    (p : Ideal ℤ) (hp0 : p ≠ ⊥) [p.IsMaximal]
    (s : Finset (Ideal (𝓞 (quadraticField D))))
    (hs : s ⊆ IsDedekindDomain.primesOverFinset p
      (𝓞 (quadraticField D))) :
    ∑ P ∈ s, Ideal.ramificationIdx p P ≤ 2 := by
  classical
  haveI : IsScalarTower ℤ (𝓞 (quadraticField D)) (quadraticField D) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ ℚ (quadraticField D) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hscalarOS : IsScalarTower ℤ (𝓞 (quadraticField D))
      (quadraticField D) := inferInstance
  have hscalarQ : IsScalarTower ℤ ℚ (quadraticField D) := inferInstance
  have hfund :
      ∑ P ∈ IsDedekindDomain.primesOverFinset p
          (𝓞 (quadraticField D)),
        Ideal.ramificationIdx p P * Ideal.inertiaDeg p P = 2 := by
    have hraw :=
      (@Ideal.sum_ramification_inertia
        ℤ _ (𝓞 (quadraticField D)) _ _ _ ℚ (quadraticField D)
        _ _ _ _ _ _ _ _ _ hscalarOS hscalarQ _ p _ hp0)
    have hrank : Module.finrank ℚ (quadraticField D) = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two ℚ (quadraticField D)
    rw [hrank] at hraw
    exact hraw
  calc
    ∑ P ∈ s, Ideal.ramificationIdx p P ≤
        ∑ P ∈ s,
          Ideal.ramificationIdx p P * Ideal.inertiaDeg p P := by
      apply Finset.sum_le_sum
      intro P hP
      have hover :=
        (IsDedekindDomain.mem_primesOverFinset_iff hp0
          (𝓞 (quadraticField D))).mp (hs hP)
      letI : P.IsPrime := hover.1
      letI : P.LiesOver p := hover.2
      exact Nat.le_mul_of_pos_right _
        (Nat.pos_iff_ne_zero.mpr (Ideal.inertiaDeg_ne_zero p P))
    _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p
          (𝓞 (quadraticField D)),
        Ideal.ramificationIdx p P * Ideal.inertiaDeg p P :=
      Finset.sum_le_sum_of_subset hs
    _ = 2 := hfund

/-- Prime-ideal support of the maximal-order principal ideal `(N)`. -/
def quadraticMaximalOrderPrimeSupport
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ) :=
  {P : Ideal (𝓞 (quadraticField D)) //
    P ∈ (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).toFinset}

noncomputable instance quadraticMaximalOrderPrimeSupportFintype
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ) :
    Fintype (quadraticMaximalOrderPrimeSupport D N) :=
  Fintype.ofFinset
    (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).toFinset
    (by intro P; rfl)

/-- The rational prime ideal below a prime in the maximal-order support. -/
noncomputable def quadraticMaximalOrderPrimeBelow
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ)
    (P : quadraticMaximalOrderPrimeSupport D N) : Ideal ℤ :=
  ((⟨P.1, (Ideal.prime_iff_isPrime
      (ne_zero_of_mem_normalizedFactors
        (Multiset.mem_toFinset.mp P.2))).mp
        (prime_of_normalized_factor P.1
          (Multiset.mem_toFinset.mp P.2)),
      ne_zero_of_mem_normalizedFactors
        (Multiset.mem_toFinset.mp P.2)⟩ :
      IsDedekindDomain.HeightOneSpectrum
        (𝓞 (quadraticField D))).under ℤ).asIdeal

/-- Every maximal-order prime occurring in `(N)` lies above a rational prime
which occurs in the factorization of the integer ideal `(N)`. -/
theorem quadraticMaximalOrderPrimeBelow_mem_intSupport
    (D : ℕ) [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    (P : quadraticMaximalOrderPrimeSupport D N) :
    quadraticMaximalOrderPrimeBelow D N P ∈
      (normalizedFactors (Ideal.span ({N} : Set ℤ))).toFinset := by
  have hcountUpper : 0 < (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).count P.1 :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.2)
  have hcount :=
    count_maximalOrder_normalizedFactors_eq_ramificationIdx_mul_count_under
      D hN (Multiset.mem_toFinset.mp P.2)
  change (normalizedFactors
    (Ideal.span ({(N : 𝓞 (quadraticField D))} :
      Set (𝓞 (quadraticField D))))).count P.1 =
      _ * (normalizedFactors (Ideal.span ({N} : Set ℤ))).count
        (quadraticMaximalOrderPrimeBelow D N P) at hcount
  apply Multiset.mem_toFinset.mpr
  apply Multiset.count_pos.mp
  have hprod : 0 < _ *
      (normalizedFactors (Ideal.span ({N} : Set ℤ))).count
        (quadraticMaximalOrderPrimeBelow D N P) := hcount ▸ hcountUpper
  rw [mul_comm] at hprod
  exact Nat.pos_of_mul_pos_right hprod

/-- The complete Euler-factor contribution above one rational prime is at
most the square of the corresponding rational Euler factor. -/
theorem quadraticMaximalOrder_fiberEulerFactor_le_sq
    (D : ℕ) [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    (p : Ideal ℤ)
    (hp : p ∈ (normalizedFactors
      (Ideal.span ({N} : Set ℤ))).toFinset) :
    ∏ P ∈ (Finset.univ.filter
        (fun P : quadraticMaximalOrderPrimeSupport D N ↦
          quadraticMaximalOrderPrimeBelow D N P = p)),
      ((normalizedFactors
        (Ideal.span ({(N : 𝓞 (quadraticField D))} :
          Set (𝓞 (quadraticField D))))).count P.1 + 1) ≤
      ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1) ^ 2 := by
  classical
  let u : Finset (quadraticMaximalOrderPrimeSupport D N) :=
    Finset.univ.filter
      (fun P ↦ quadraticMaximalOrderPrimeBelow D N P = p)
  let s : Finset (Ideal (𝓞 (quadraticField D))) := u.image Subtype.val
  have hp0 : p ≠ ⊥ :=
    ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)
  have hpPrime : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp
    (prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp))
  letI : p.IsMaximal := hpPrime.isMaximal hp0
  have hs : s ⊆ IsDedekindDomain.primesOverFinset p
      (𝓞 (quadraticField D)) := by
    intro Q hQ
    obtain ⟨P, hPu, rfl⟩ := Finset.mem_image.mp hQ
    have hPbelow : quadraticMaximalOrderPrimeBelow D N P = p :=
      (Finset.mem_filter.mp hPu).2
    have hPmem := Multiset.mem_toFinset.mp P.2
    have hP0 : P.1 ≠ ⊥ := ne_zero_of_mem_normalizedFactors hPmem
    have hPPrime : P.1.IsPrime := (Ideal.prime_iff_isPrime hP0).mp
      (prime_of_normalized_factor P.1 hPmem)
    apply (IsDedekindDomain.mem_primesOverFinset_iff hp0
      (𝓞 (quadraticField D))).mpr
    refine ⟨hPPrime, ?_⟩
    constructor
    change p = quadraticMaximalOrderPrimeBelow D N P
    exact hPbelow.symm
  have hsumS : ∑ Q ∈ s, Ideal.ramificationIdx p Q ≤ 2 :=
    sum_ramificationIdx_subset_le_two D p hp0 s hs
  have hsumU : ∑ P ∈ u, Ideal.ramificationIdx p P.1 ≤ 2 := by
    calc
      ∑ P ∈ u, Ideal.ramificationIdx p P.1 =
          ∑ Q ∈ s, Ideal.ramificationIdx p Q := by
        dsimp only [s]
        rw [Finset.sum_image]
        · rfl
        · exact Set.injOn_of_injective Subtype.val_injective
      _ ≤ 2 := hsumS
  change ∏ P ∈ u, _ ≤ _
  calc
    ∏ P ∈ u,
        ((normalizedFactors
          (Ideal.span ({(N : 𝓞 (quadraticField D))} :
            Set (𝓞 (quadraticField D))))).count P.1 + 1) =
        ∏ P ∈ u, (Ideal.ramificationIdx p P.1 *
          (normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1) := by
      apply Finset.prod_congr rfl
      intro P hPu
      have hPbelow : quadraticMaximalOrderPrimeBelow D N P = p :=
        (Finset.mem_filter.mp hPu).2
      have hcount :=
        count_maximalOrder_normalizedFactors_eq_ramificationIdx_mul_count_under
          D hN (Multiset.mem_toFinset.mp P.2)
      change (normalizedFactors
        (Ideal.span ({(N : 𝓞 (quadraticField D))} :
          Set (𝓞 (quadraticField D))))).count P.1 =
        Ideal.ramificationIdx
          (quadraticMaximalOrderPrimeBelow D N P) P.1 *
          (normalizedFactors (Ideal.span ({N} : Set ℤ))).count
            (quadraticMaximalOrderPrimeBelow D N P) at hcount
      rw [hPbelow] at hcount
      omega
    _ ≤ ∏ P ∈ u,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1) ^
          Ideal.ramificationIdx p P.1 := by
      apply Finset.prod_le_prod'
      intro P hPu
      simpa [add_comm, mul_comm] using
        (one_add_mul_le_pow_of_sq_nonneg (a :=
          (normalizedFactors (Ideal.span ({N} : Set ℤ))).count p)
          (by positivity) (by positivity) (by positivity)
          (Ideal.ramificationIdx p P.1))
    _ = ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1) ^
        (∑ P ∈ u, Ideal.ramificationIdx p P.1) := by
      exact Finset.prod_pow_eq_pow_sum u
        (fun P ↦ Ideal.ramificationIdx p P.1)
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1)
    _ ≤ ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1) ^ 2 :=
      Nat.pow_le_pow_right (by omega) hsumU

/-- Multiplying the sharp bounds over rational primes gives the quadratic
extension comparison between the maximal-order and rational Euler products. -/
theorem prod_maximalOrder_normalizedFactors_le_prod_intIdeal_sq
    (D : ℕ) [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0) :
    ∏ P ∈ (normalizedFactors
        (Ideal.span ({(N : 𝓞 (quadraticField D))} :
          Set (𝓞 (quadraticField D))))).toFinset,
      ((normalizedFactors
        (Ideal.span ({(N : 𝓞 (quadraticField D))} :
          Set (𝓞 (quadraticField D))))).count P + 1) ≤
      (∏ p ∈ (normalizedFactors
          (Ideal.span ({N} : Set ℤ))).toFinset,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1)) ^ 2 := by
  classical
  let upper : Finset (Ideal (𝓞 (quadraticField D))) :=
    (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).toFinset
  let base : Finset (Ideal ℤ) :=
    (normalizedFactors (Ideal.span ({N} : Set ℤ))).toFinset
  let f : quadraticMaximalOrderPrimeSupport D N → ℕ := fun P ↦
    (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).count P.1 + 1
  have hmaps :
      ∀ P ∈ (Finset.univ : Finset (quadraticMaximalOrderPrimeSupport D N)),
        quadraticMaximalOrderPrimeBelow D N P ∈ base := by
    intro P _
    exact quadraticMaximalOrderPrimeBelow_mem_intSupport D hN P
  have hfiber := Finset.prod_fiberwise_of_maps_to hmaps f
  change ∏ P ∈ upper, _ ≤ (∏ p ∈ base, _) ^ 2
  calc
    ∏ P ∈ upper,
        ((normalizedFactors
          (Ideal.span ({(N : 𝓞 (quadraticField D))} :
            Set (𝓞 (quadraticField D))))).count P + 1) =
        ∏ P ∈
          (Finset.univ : Finset (quadraticMaximalOrderPrimeSupport D N)),
          f P := by
      dsimp only [upper, f]
      exact Finset.prod_subtype
        (normalizedFactors
          (Ideal.span ({(N : 𝓞 (quadraticField D))} :
            Set (𝓞 (quadraticField D))))).toFinset
        (fun _ ↦ Iff.rfl)
        (fun P ↦ (normalizedFactors
          (Ideal.span ({(N : 𝓞 (quadraticField D))} :
            Set (𝓞 (quadraticField D))))).count P + 1)
    _ = ∏ p ∈ base,
        ∏ P ∈
          (Finset.univ : Finset (quadraticMaximalOrderPrimeSupport D N)) with
          quadraticMaximalOrderPrimeBelow D N P = p, f P := hfiber.symm
    _ ≤ ∏ p ∈ base,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1) ^ 2 := by
      apply Finset.prod_le_prod'
      intro p hp
      exact quadraticMaximalOrder_fiberEulerFactor_le_sq D hN p hp
    _ = (∏ p ∈ base,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1)) ^ 2 := by
      rw [Finset.prod_pow]

/-- Tao's sharp quadratic ideal-divisor estimate: the number of ideal
divisors of `(N)` in `𝓞(ℚ(√D))` is at most `d(|N|)^2`. -/
theorem card_maximalOrderIdealDivisors_le_card_divisors_sq
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ) (hN : N ≠ 0) :
    (maximalOrderIdealDivisors D N hN).card ≤
      N.natAbs.divisors.card ^ 2 := by
  calc
    (maximalOrderIdealDivisors D N hN).card ≤
        ∏ P ∈ (normalizedFactors
          (Ideal.span ({(N : 𝓞 (quadraticField D))} :
            Set (𝓞 (quadraticField D))))).toFinset,
          ((normalizedFactors
            (Ideal.span ({(N : 𝓞 (quadraticField D))} :
              Set (𝓞 (quadraticField D))))).count P + 1) :=
      card_maximalOrderIdealDivisors_le_prod_normalizedFactors D N hN
    _ ≤ (∏ p ∈ (normalizedFactors
          (Ideal.span ({N} : Set ℤ))).toFinset,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1)) ^ 2 :=
      prod_maximalOrder_normalizedFactors_le_prod_intIdeal_sq D hN
    _ = N.natAbs.divisors.card ^ 2 := by
      rw [prod_intIdeal_normalizedFactors_eq_card_divisors N hN]

end Tao2026

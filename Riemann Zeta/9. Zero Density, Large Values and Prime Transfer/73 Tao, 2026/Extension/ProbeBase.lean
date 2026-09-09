import Tao2026.QuadraticSolutionCount

open scoped NumberField
open UniqueFactorizationMonoid

#check Fintype.prod_equiv
#check Equiv.prod_comp
#check Finset.prod_bij
#check Finset.prod_equiv
#check UniqueFactorizationMonoid.primeFactors
#check UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs
#check factorization_eq_count
#check UniqueFactorizationMonoid.primeFactors
#check UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors
#check Nat.factorization
#check factorization
#check Nat.factorization_eq_primeFactorsList_multiset
#check Int.emultiplicity_natAbs
#check Nat.card_divisors
#check Ideal.normalizedFactorsEquivSpanNormalizedFactors
#check Ideal.count_span_normalizedFactors_eq
#check Nat.prime_iff
#check Nat.prime_iff_prime_int
#check Prime.irreducible
#check Int.normalize_coe_nat
#check Finset.prod_attach
example (n p : ℕ) :
    Multiset.count p (normalizedFactors n) = n.factorization p := by
  rw [← factorization_eq_count]
  change Multiset.toFinsupp (normalizedFactors n) p = n.factorization p
  rw [Nat.factorization_eq_primeFactorsList_multiset]
  rw [Nat.factors_eq]

example (N : ℤ) (hN : N ≠ 0) (p : ℕ) (hp : p.Prime) :
    (normalizedFactors N).count (p : ℤ) =
      (normalizedFactors N.natAbs).count p := by
  have h := Int.emultiplicity_natAbs p N
  rw [emultiplicity_eq_count_normalizedFactors
        (Nat.prime_iff.mp hp).irreducible
        (Int.natAbs_ne_zero.mpr hN),
    emultiplicity_eq_count_normalizedFactors
      ((Nat.prime_iff_prime_int.mp hp).irreducible) hN] at h
  simpa [Int.normalize_coe_nat] using h.symm

theorem probe_prod_span_int (N : ℤ) (hN : N ≠ 0) :
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

theorem probe_prod_int_card_divisors (N : ℤ) (hN : N ≠ 0) :
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

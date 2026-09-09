import Tao2026.QuadraticIdealDivisors

namespace Tao2026

open scoped NumberField
open UniqueFactorizationMonoid



theorem probe_count_under
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
    dsimp only [I]
    rw [Ideal.map_span]
    congr 1
    ext x
    simp
  rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible (hmap ▸ (by
        simpa only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
          using Int.cast_ne_zero.mpr hN)),
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible hI, hmap] at hem
  simp only [normalize_eq, I] at hem
  exact_mod_cast hem

theorem probe_count_under_le_two
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
  have htest : IsScalarTower ℤ (𝓞 (quadraticField D)) (quadraticField D) :=
    inferInstance
  have hram : v.asIdeal.ramificationIdx w.asIdeal ≤ 2 := by
    simpa only [Algebra.IsQuadraticExtension.finrank_eq_two] using
      (@Ideal.ramificationIdx_le_finrank
        ℤ _ (𝓞 (quadraticField D)) _ _ _ ℚ (quadraticField D)
        _ _ _ _ _ _ _ _ _ htest _ _ _ v.asIdeal _ w.asIdeal _ _)
  rw [probe_count_under D hN hPmem]
  exact Nat.mul_le_mul_right _ hram

theorem probe_sum_ramificationIdx_subset_le_two
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

def probeUpperSupport
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ) :=
  {P : Ideal (𝓞 (quadraticField D)) //
    P ∈ (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).toFinset}

noncomputable instance probeUpperSupportFintype
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ) :
  Fintype (probeUpperSupport D N) :=
  Fintype.ofFinset
    (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).toFinset
    (by intro P; rfl)

noncomputable def probeBelow
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ)
    (P : probeUpperSupport D N) : Ideal ℤ :=
  ((⟨P.1, (Ideal.prime_iff_isPrime
      (ne_zero_of_mem_normalizedFactors
        (Multiset.mem_toFinset.mp P.2))).mp
        (prime_of_normalized_factor P.1
          (Multiset.mem_toFinset.mp P.2)),
      ne_zero_of_mem_normalizedFactors
        (Multiset.mem_toFinset.mp P.2)⟩ :
      IsDedekindDomain.HeightOneSpectrum
        (𝓞 (quadraticField D))).under ℤ).asIdeal

theorem probeBelow_mem_baseSupport
    (D : ℕ) [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    (P : probeUpperSupport D N) :
    probeBelow D N P ∈
      (normalizedFactors (Ideal.span ({N} : Set ℤ))).toFinset := by
  have hcountUpper : 0 < (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).count P.1 :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.2)
  have hcount := probe_count_under D hN (Multiset.mem_toFinset.mp P.2)
  change (normalizedFactors
    (Ideal.span ({(N : 𝓞 (quadraticField D))} :
      Set (𝓞 (quadraticField D))))).count P.1 =
      _ * (normalizedFactors (Ideal.span ({N} : Set ℤ))).count
        (probeBelow D N P) at hcount
  apply Multiset.mem_toFinset.mpr
  apply Multiset.count_pos.mp
  have hprod : 0 < _ *
      (normalizedFactors (Ideal.span ({N} : Set ℤ))).count
        (probeBelow D N P) := hcount ▸ hcountUpper
  rw [mul_comm] at hprod
  exact Nat.pos_of_mul_pos_right hprod

theorem probe_fiber_prod_le_sq
    (D : ℕ) [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    (p : Ideal ℤ)
    (hp : p ∈ (normalizedFactors
      (Ideal.span ({N} : Set ℤ))).toFinset) :
    ∏ P ∈ (Finset.univ.filter
        (fun P : probeUpperSupport D N ↦ probeBelow D N P = p)),
      ((normalizedFactors
        (Ideal.span ({(N : 𝓞 (quadraticField D))} :
          Set (𝓞 (quadraticField D))))).count P.1 + 1) ≤
      ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1) ^ 2 := by
  classical
  let u : Finset (probeUpperSupport D N) := Finset.univ.filter
    (fun P ↦ probeBelow D N P = p)
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
    have hPbelow : probeBelow D N P = p :=
      (Finset.mem_filter.mp hPu).2
    have hPmem := Multiset.mem_toFinset.mp P.2
    have hP0 : P.1 ≠ ⊥ := ne_zero_of_mem_normalizedFactors hPmem
    have hPPrime : P.1.IsPrime := (Ideal.prime_iff_isPrime hP0).mp
      (prime_of_normalized_factor P.1 hPmem)
    apply (IsDedekindDomain.mem_primesOverFinset_iff hp0
      (𝓞 (quadraticField D))).mpr
    refine ⟨hPPrime, ?_⟩
    constructor
    change p = probeBelow D N P
    exact hPbelow.symm
  have hsumS : ∑ Q ∈ s, Ideal.ramificationIdx p Q ≤ 2 :=
    probe_sum_ramificationIdx_subset_le_two D p hp0 s hs
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
      have hPbelow : probeBelow D N P = p :=
        (Finset.mem_filter.mp hPu).2
      have hcount := probe_count_under D hN
        (Multiset.mem_toFinset.mp P.2)
      change (normalizedFactors
        (Ideal.span ({(N : 𝓞 (quadraticField D))} :
          Set (𝓞 (quadraticField D))))).count P.1 =
        Ideal.ramificationIdx (probeBelow D N P) P.1 *
          (normalizedFactors (Ideal.span ({N} : Set ℤ))).count
            (probeBelow D N P) at hcount
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

theorem probe_upper_prod_le_base_prod_sq
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
  let f : probeUpperSupport D N → ℕ := fun P ↦
    (normalizedFactors
      (Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D))))).count P.1 + 1
  have hmaps : ∀ P ∈ (Finset.univ : Finset (probeUpperSupport D N)),
      probeBelow D N P ∈ base := by
    intro P _
    exact probeBelow_mem_baseSupport D hN P
  have hfiber := Finset.prod_fiberwise_of_maps_to hmaps f
  change ∏ P ∈ upper, _ ≤ (∏ p ∈ base, _) ^ 2
  calc
    ∏ P ∈ upper,
        ((normalizedFactors
          (Ideal.span ({(N : 𝓞 (quadraticField D))} :
            Set (𝓞 (quadraticField D))))).count P + 1) =
        ∏ P ∈ (Finset.univ : Finset (probeUpperSupport D N)), f P := by
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
        ∏ P ∈ (Finset.univ : Finset (probeUpperSupport D N)) with
          probeBelow D N P = p, f P := hfiber.symm
    _ ≤ ∏ p ∈ base,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1) ^ 2 := by
      apply Finset.prod_le_prod'
      intro p hp
      exact probe_fiber_prod_le_sq D hN p hp
    _ = (∏ p ∈ base,
        ((normalizedFactors (Ideal.span ({N} : Set ℤ))).count p + 1)) ^ 2 := by
      rw [Finset.prod_pow]

end Tao2026

import RiemannZeta.GuthMaynard.KloostermanFactorization

open Polynomial Classical
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

noncomputable section


/-- The `HarcosPrimeUpTo` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
def HarcosPrimeUpTo (p n : ℕ) [Fact p.Prime] :=
  {q : HarcosIrreducibleMonic p // q.1.natDegree ≤ n}

noncomputable instance harcosPrimeUpToFintype
    (p n : ℕ) [Fact p.Prime] : Fintype (HarcosPrimeUpTo p n) := by
  let f : HarcosPrimeUpTo p n → (Fin (n + 1) → ZMod p) :=
    fun q i ↦ q.1.1.coeff i
  apply Fintype.ofInjective f
  intro q r h
  apply Subtype.ext
  apply Subtype.ext
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ n
  · have heq := congrFun h ⟨i, Nat.lt_succ_iff.mpr hi⟩
    exact heq
  · have hni : n < i := Nat.lt_of_not_ge hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt q.2 hni),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt r.2 hni)]

theorem harcosPrimeUpTo_degree_pos
    (p n : ℕ) [Fact p.Prime] (q : HarcosPrimeUpTo p n) :
    0 < q.1.1.natDegree := q.1.2.1.natDegree_pos

/-- The `harcosPrimeGeometricSeries` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
noncomputable def harcosPrimeGeometricSeries
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (q : HarcosPrimeUpTo p n) : PowerSeries ℂ :=
  PowerSeries.mk fun j ↦
    if q.1.1.natDegree ∣ j then
      harcosEtaPolynomial p a b q.1.1 ^ (j / q.1.1.natDegree)
    else 0

@[simp] theorem coeff_harcosPrimeGeometricSeries
    (p n j : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (q : HarcosPrimeUpTo p n) :
    PowerSeries.coeff j (harcosPrimeGeometricSeries p n a b q) =
      if q.1.1.natDegree ∣ j then
        harcosEtaPolynomial p a b q.1.1 ^ (j / q.1.1.natDegree)
      else 0 := by
  simp [harcosPrimeGeometricSeries]

/-- The `harcosFiniteEulerProduct` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
noncomputable def harcosFiniteEulerProduct
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) : PowerSeries ℂ :=
  ∏ q : HarcosPrimeUpTo p n, harcosPrimeGeometricSeries p n a b q

/-- The `harcosPrimeUpToOfFactor` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
noncomputable def harcosPrimeUpToOfFactor
    (p n : ℕ) [Fact p.Prime] (s : HarcosFactorization p n)
    (q : HarcosIrreducibleMonic p) (hq : q ∈ s.1) :
    HarcosPrimeUpTo p n :=
  ⟨q, by
    rw [← s.2]
    apply Multiset.le_sum_of_mem
    exact Multiset.mem_map.mpr ⟨q, hq, rfl⟩⟩

theorem sum_harcosPrimeUpTo_count_mul_degree
    (p n : ℕ) [Fact p.Prime] (s : HarcosFactorization p n) :
    ∑ q : HarcosPrimeUpTo p n,
        s.1.count q.1 * q.1.1.natDegree = n := by
  let e : {q // q ∈ s.1.toFinset} → HarcosPrimeUpTo p n :=
    fun q ↦ harcosPrimeUpToOfFactor p n s q.1
      (Multiset.mem_toFinset.mp q.2)
  have he : Function.Injective e := by
    intro q r h
    apply Subtype.ext
    exact congrArg (fun z : HarcosPrimeUpTo p n ↦ z.1) h
  let t : Finset (HarcosPrimeUpTo p n) :=
    s.1.toFinset.attach.image e
  calc
    ∑ q : HarcosPrimeUpTo p n,
        s.1.count q.1 * q.1.1.natDegree =
        ∑ q ∈ t, s.1.count q.1 * q.1.1.natDegree := by
      symm
      apply Finset.sum_subset (Finset.subset_univ t)
      intro q _hq hqt
      have hnot : q.1 ∉ s.1 := by
        intro hmem
        apply hqt
        apply Finset.mem_image.mpr
        refine ⟨⟨q.1, by simpa using hmem⟩, by simp, ?_⟩
        apply Subtype.ext
        rfl
      rw [Multiset.count_eq_zero.mpr hnot]
      simp
    _ = ∑ q ∈ s.1.toFinset,
        s.1.count q * q.1.natDegree := by
      dsimp [t]
      rw [Finset.sum_image he.injOn]
      exact Finset.sum_attach s.1.toFinset
        (fun q ↦ s.1.count q * q.1.natDegree)
    _ = (s.1.map (fun q ↦ q.1.natDegree)).sum := by
      rw [Finset.sum_multiset_map_count]
      simp [mul_comm]
    _ = n := s.2

/-- The `HarcosEulerAllocation` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
def HarcosEulerAllocation (p n : ℕ) [Fact p.Prime] :=
  {l : HarcosPrimeUpTo p n →₀ ℕ //
    l ∈ Finset.finsuppAntidiag Finset.univ n ∧
      ∀ q, q.1.1.natDegree ∣ l q}

/-- The `harcosEulerAllocationOfFactorization` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
noncomputable def harcosEulerAllocationOfFactorization
    (p n : ℕ) [Fact p.Prime] (s : HarcosFactorization p n) :
    HarcosEulerAllocation p n := by
  let l : HarcosPrimeUpTo p n →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm
      (fun q ↦ s.1.count q.1 * q.1.1.natDegree)
  refine ⟨l, ?_, ?_⟩
  · rw [Finset.mem_finsuppAntidiag]
    constructor
    · simpa [l] using sum_harcosPrimeUpTo_count_mul_degree p n s
    · exact Finset.subset_univ _
  · intro q
    change q.1.1.natDegree ∣ s.1.count q.1 * q.1.1.natDegree
    exact dvd_mul_left _ _

/-- The `harcosFactorizationOfEulerAllocation` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
noncomputable def harcosFactorizationOfEulerAllocation
    (p n : ℕ) [Fact p.Prime] (l : HarcosEulerAllocation p n) :
    HarcosFactorization p n := by
  let s : Multiset (HarcosIrreducibleMonic p) :=
    ∑ q : HarcosPrimeUpTo p n,
      Multiset.replicate (l.1 q / q.1.1.natDegree) q.1
  refine ⟨s, ?_⟩
  have hsum : ∑ q : HarcosPrimeUpTo p n, l.1 q = n := by
    exact (Finset.mem_finsuppAntidiag.mp l.2.1).1
  have hmapSum :
      (s.map (fun q ↦ q.1.natDegree)) =
        ∑ q : HarcosPrimeUpTo p n,
          (Multiset.replicate (l.1 q / q.1.1.natDegree) q.1).map
            (fun r ↦ r.1.natDegree) := by
    dsimp [s]
    exact map_sum (Multiset.mapAddMonoidHom (fun q ↦ q.1.natDegree))
      (fun q : HarcosPrimeUpTo p n ↦
        Multiset.replicate (l.1 q / q.1.1.natDegree) q.1) Finset.univ
  calc
    (s.map (fun q ↦ q.1.natDegree)).sum =
        ∑ q : HarcosPrimeUpTo p n,
          (l.1 q / q.1.1.natDegree) * q.1.1.natDegree := by
      rw [hmapSum]
      change Multiset.sumAddMonoidHom
          (∑ q : HarcosPrimeUpTo p n,
            (Multiset.replicate (l.1 q / q.1.1.natDegree) q.1).map
              (fun r ↦ r.1.natDegree)) = _
      rw [map_sum (Multiset.sumAddMonoidHom)]
      simp [Multiset.map_replicate, mul_comm]
    _ = ∑ q : HarcosPrimeUpTo p n, l.1 q := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact Nat.div_mul_cancel (l.2.2 q)
    _ = n := hsum

theorem count_harcosFactorizationOfEulerAllocation
    (p n : ℕ) [Fact p.Prime] (l : HarcosEulerAllocation p n)
    (q : HarcosIrreducibleMonic p) :
    (harcosFactorizationOfEulerAllocation p n l).1.count q =
      if hq : q.1.natDegree ≤ n then
        l.1 (⟨q, hq⟩ : HarcosPrimeUpTo p n) / q.1.natDegree
      else 0 := by
  classical
  let countHom : Multiset (HarcosIrreducibleMonic p) →+ ℕ :=
    { toFun := fun m : Multiset (HarcosIrreducibleMonic p) ↦ Multiset.count q m
      map_zero' := Multiset.count_zero q
      map_add' := fun u v ↦ Multiset.count_add q u v }
  change countHom
      (∑ r : HarcosPrimeUpTo p n,
        Multiset.replicate (l.1 r / r.1.1.natDegree) r.1) = _
  rw [map_sum countHom]
  by_cases hq : q.1.natDegree ≤ n
  · rw [dif_pos hq]
    let q' : HarcosPrimeUpTo p n := ⟨q, hq⟩
    rw [Finset.sum_eq_single q']
    · simp [countHom, q']
    · intro r _hr hrq
      change Multiset.count q
        (Multiset.replicate (l.1 r / r.1.1.natDegree) r.1) = 0
      rw [Multiset.count_replicate]
      rw [if_neg]
      intro h
      apply hrq
      apply Subtype.ext
      exact h
    · simp
  · rw [dif_neg hq]
    apply Finset.sum_eq_zero
    intro r _hr
    change Multiset.count q
      (Multiset.replicate (l.1 r / r.1.1.natDegree) r.1) = 0
    rw [Multiset.count_replicate]
    rw [if_neg]
    intro hr
    apply hq
    simpa [hr] using r.2

theorem harcosEulerAllocation_factorization_left
    (p n : ℕ) [Fact p.Prime] (s : HarcosFactorization p n) :
    harcosFactorizationOfEulerAllocation p n
      (harcosEulerAllocationOfFactorization p n s) = s := by
  apply Subtype.ext
  apply Multiset.ext.mpr
  intro q
  rw [count_harcosFactorizationOfEulerAllocation]
  by_cases hq : q ∈ s.1
  · have hdeg : q.1.natDegree ≤ n := by
      rw [← s.2]
      apply Multiset.le_sum_of_mem
      exact Multiset.mem_map.mpr ⟨q, hq, rfl⟩
    rw [dif_pos hdeg]
    change (s.1.count q * q.1.natDegree) / q.1.natDegree = s.1.count q
    rw [mul_comm, Nat.mul_div_cancel_left _
      (harcosPrimeUpTo_degree_pos p n ⟨q, hdeg⟩)]
  · have hcount : s.1.count q = 0 := Multiset.count_eq_zero.mpr hq
    split
    · change (s.1.count q * q.1.natDegree) / q.1.natDegree = s.1.count q
      rw [hcount]
      simp
    · exact hcount.symm

theorem harcosEulerAllocation_factorization_right
    (p n : ℕ) [Fact p.Prime] (l : HarcosEulerAllocation p n) :
    harcosEulerAllocationOfFactorization p n
      (harcosFactorizationOfEulerAllocation p n l) = l := by
  apply Subtype.ext
  apply Finsupp.ext
  intro q
  change (harcosFactorizationOfEulerAllocation p n l).1.count q.1 *
      q.1.1.natDegree = l.1 q
  rw [count_harcosFactorizationOfEulerAllocation, dif_pos q.2]
  exact Nat.div_mul_cancel (l.2.2 q)

/-- The `harcosEulerAllocationEquiv` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
def harcosEulerAllocationEquiv
    (p n : ℕ) [Fact p.Prime] :
    HarcosFactorization p n ≃ HarcosEulerAllocation p n where
  toFun := harcosEulerAllocationOfFactorization p n
  invFun := harcosFactorizationOfEulerAllocation p n
  left_inv := harcosEulerAllocation_factorization_left p n
  right_inv := harcosEulerAllocation_factorization_right p n

noncomputable instance harcosEulerAllocationFintype
    (p n : ℕ) [Fact p.Prime] : Fintype (HarcosEulerAllocation p n) :=
  Fintype.ofEquiv (HarcosFactorization p n)
    (harcosEulerAllocationEquiv p n)

/-- The `harcosEulerAllocationWeight` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
noncomputable def harcosEulerAllocationWeight
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (l : HarcosEulerAllocation p n) : ℂ :=
  ∏ q : HarcosPrimeUpTo p n,
    harcosEtaPolynomial p a b q.1.1 ^
      (l.1 q / q.1.1.natDegree)

theorem prod_map_sum_replicate
    {α β γ : Type*} [DecidableEq α] [CommMonoid β]
    (u : Finset α) (e : α → ℕ) (y : α → γ) (x : γ → β) :
    (((∑ q ∈ u, Multiset.replicate (e q) (y q)).map x).prod) =
      ∏ q ∈ u, x (y q) ^ e q := by
  induction u using Finset.induction_on with
  | empty => simp
  | @insert q u hq ih =>
      simp only [Finset.sum_insert hq, Multiset.map_add,
        Multiset.prod_add, Finset.prod_insert hq]
      rw [ih]
      simp

theorem harcosFactorizationWeight_ofEulerAllocation
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (l : HarcosEulerAllocation p n) :
    harcosFactorizationWeight p n a b
        (harcosFactorizationOfEulerAllocation p n l) =
      harcosEulerAllocationWeight p n a b l := by
  unfold harcosFactorizationWeight harcosEulerAllocationWeight
  change (((∑ q : HarcosPrimeUpTo p n,
      Multiset.replicate (l.1 q / q.1.1.natDegree) q.1).map
        (fun q ↦ harcosEtaPolynomial p a b q.1)).prod) = _
  exact prod_map_sum_replicate Finset.univ
    (fun q : HarcosPrimeUpTo p n ↦ l.1 q / q.1.1.natDegree)
    (fun q ↦ q.1)
    (fun q ↦ harcosEtaPolynomial p a b q.1)

theorem coeff_harcosFiniteEulerProduct_raw
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    PowerSeries.coeff n (harcosFiniteEulerProduct p n a b) =
      ∑ l ∈ Finset.finsuppAntidiag
          (Finset.univ : Finset (HarcosPrimeUpTo p n)) n,
        ∏ q : HarcosPrimeUpTo p n,
          if q.1.1.natDegree ∣ l q then
            harcosEtaPolynomial p a b q.1.1 ^
              (l q / q.1.1.natDegree)
          else 0 := by
  unfold harcosFiniteEulerProduct
  rw [show (∏ q : HarcosPrimeUpTo p n,
      harcosPrimeGeometricSeries p n a b q) =
      ∏ q ∈ (Finset.univ : Finset (HarcosPrimeUpTo p n)),
        harcosPrimeGeometricSeries p n a b q by simp]
  rw [PowerSeries.coeff_prod]
  simp only [coeff_harcosPrimeGeometricSeries]

/-- The `harcosEulerAllocationFinset` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
def harcosEulerAllocationFinset
    (p n : ℕ) [Fact p.Prime] :
    Finset (HarcosPrimeUpTo p n →₀ ℕ) :=
  (Finset.finsuppAntidiag
    (Finset.univ : Finset (HarcosPrimeUpTo p n)) n).filter
      (fun l ↦ ∀ q, q.1.1.natDegree ∣ l q)

/-- The `harcosEulerAllocationSubtypeEquiv` definition used by the source-facing construction in `KloostermanLocalEuler`. -/
def harcosEulerAllocationSubtypeEquiv
    (p n : ℕ) [Fact p.Prime] :
    {l // l ∈ harcosEulerAllocationFinset p n} ≃
      HarcosEulerAllocation p n where
  toFun l :=
    ⟨l.1, (Finset.mem_filter.mp l.2).1,
      (Finset.mem_filter.mp l.2).2⟩
  invFun l :=
    ⟨l.1, Finset.mem_filter.mpr ⟨l.2.1, l.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem harcosEulerProductTerm_eq_weight
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (l : HarcosPrimeUpTo p n →₀ ℕ)
    (hl : ∀ q, q.1.1.natDegree ∣ l q) :
    (∏ q : HarcosPrimeUpTo p n,
        if q.1.1.natDegree ∣ l q then
          harcosEtaPolynomial p a b q.1.1 ^
            (l q / q.1.1.natDegree)
        else 0) =
      ∏ q : HarcosPrimeUpTo p n,
        harcosEtaPolynomial p a b q.1.1 ^
          (l q / q.1.1.natDegree) := by
  apply Finset.prod_congr rfl
  intro q _hq
  rw [if_pos (hl q)]

theorem harcosEulerProductTerm_eq_zero
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (l : HarcosPrimeUpTo p n →₀ ℕ)
    (hl : ¬ ∀ q, q.1.1.natDegree ∣ l q) :
    (∏ q : HarcosPrimeUpTo p n,
        if q.1.1.natDegree ∣ l q then
          harcosEtaPolynomial p a b q.1.1 ^
            (l q / q.1.1.natDegree)
        else 0) = 0 := by
  push Not at hl
  obtain ⟨q, hq⟩ := hl
  apply Finset.prod_eq_zero (Finset.mem_univ q)
  rw [if_neg hq]

theorem sum_harcosEulerAllocationWeight_eq_finset
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    (∑ l : HarcosEulerAllocation p n,
        harcosEulerAllocationWeight p n a b l) =
      ∑ l ∈ harcosEulerAllocationFinset p n,
        ∏ q : HarcosPrimeUpTo p n,
          harcosEtaPolynomial p a b q.1.1 ^
            (l q / q.1.1.natDegree) := by
  symm
  calc
    (∑ l ∈ harcosEulerAllocationFinset p n,
        ∏ q : HarcosPrimeUpTo p n,
          harcosEtaPolynomial p a b q.1.1 ^
            (l q / q.1.1.natDegree)) =
        ∑ l : {l // l ∈ harcosEulerAllocationFinset p n},
          ∏ q : HarcosPrimeUpTo p n,
            harcosEtaPolynomial p a b q.1.1 ^
              (l.1 q / q.1.1.natDegree) := by
      apply Finset.sum_subtype
      intro l
      rfl
    _ = ∑ l : HarcosEulerAllocation p n,
        harcosEulerAllocationWeight p n a b l := by
      apply Fintype.sum_equiv
        (harcosEulerAllocationSubtypeEquiv p n)
      intro l
      rfl

theorem coeff_harcosFiniteEulerProduct_eq_allocationSum
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    PowerSeries.coeff n (harcosFiniteEulerProduct p n a b) =
      ∑ l : HarcosEulerAllocation p n,
        harcosEulerAllocationWeight p n a b l := by
  rw [coeff_harcosFiniteEulerProduct_raw]
  rw [sum_harcosEulerAllocationWeight_eq_finset]
  let s := Finset.finsuppAntidiag
    (Finset.univ : Finset (HarcosPrimeUpTo p n)) n
  let t := harcosEulerAllocationFinset p n
  calc
    (∑ l ∈ s,
        ∏ q : HarcosPrimeUpTo p n,
          if q.1.1.natDegree ∣ l q then
            harcosEtaPolynomial p a b q.1.1 ^
              (l q / q.1.1.natDegree)
          else 0) =
        ∑ l ∈ t,
          ∏ q : HarcosPrimeUpTo p n,
            if q.1.1.natDegree ∣ l q then
              harcosEtaPolynomial p a b q.1.1 ^
                (l q / q.1.1.natDegree)
            else 0 := by
      symm
      apply Finset.sum_subset
      · exact Finset.filter_subset _ _
      · intro l hls hlt
        apply harcosEulerProductTerm_eq_zero p n a b l
        intro hall
        apply hlt
        exact Finset.mem_filter.mpr ⟨hls, hall⟩
    _ = ∑ l ∈ t,
        ∏ q : HarcosPrimeUpTo p n,
          harcosEtaPolynomial p a b q.1.1 ^
            (l q / q.1.1.natDegree) := by
      apply Finset.sum_congr rfl
      intro l hlt
      apply harcosEulerProductTerm_eq_weight p n a b l
      exact (Finset.mem_filter.mp hlt).2

theorem coeff_harcosFiniteEulerProduct_eq_factorizationSum
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    PowerSeries.coeff n (harcosFiniteEulerProduct p n a b) =
      ∑ s : HarcosFactorization p n,
        harcosFactorizationWeight p n a b s := by
  rw [coeff_harcosFiniteEulerProduct_eq_allocationSum]
  symm
  apply Fintype.sum_equiv (harcosEulerAllocationEquiv p n)
  intro s
  calc
    harcosFactorizationWeight p n a b s =
        harcosFactorizationWeight p n a b
          (harcosFactorizationOfEulerAllocation p n
            (harcosEulerAllocationEquiv p n s)) := by
      congr 1
      exact (harcosEulerAllocation_factorization_left p n s).symm
    _ = harcosEulerAllocationWeight p n a b
          (harcosEulerAllocationEquiv p n s) :=
      harcosFactorizationWeight_ofEulerAllocation p n a b _

theorem harcosEquationNine_coefficient
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    PowerSeries.coeff n (harcosFiniteEulerProduct p n a b) =
      PowerSeries.coeff n (harcosLSeries p a b) := by
  rw [coeff_harcosFiniteEulerProduct_eq_factorizationSum]
  rw [← harcosEtaDegreeSum_eq_factorizationSum]
  simp [harcosLSeries]

end

end RiemannZeta.GuthMaynard

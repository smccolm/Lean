import Tao2026.BurgessWeilPrimeKummerHasseDavenportIrreducibleEuler
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Monic factorization and the irreducible Hasse--Davenport Euler product

This file identifies the degree-`n` coefficient of the bounded irreducible
Euler product with the sum of the Hasse--Davenport weight over all monic
degree-`n` polynomials, provided the irreducible cutoff is at least `n`.

The proof passes through a multiset of normalized monic irreducible factors.
It constructs mutually inverse equivalences between monic polynomials,
factor multisets, and the divisible degree allocations occurring in the
formal Euler-product coefficient.
-/

open Polynomial Classical
open scoped BigOperators

noncomputable section

namespace Tao2026

/-- A monic irreducible polynomial, with no degree cutoff. -/
def HasseDavenportMonicIrreduciblePolynomialAny
    (K : Type*) [Field K] :=
  {q : Polynomial K // q.Monic ∧ Irreducible q}

/-- A multiset of monic irreducible polynomials whose degrees sum to `n`. -/
def HasseDavenportIrreducibleFactorization
    (K : Type*) [Field K] (n : ℕ) :=
  {s : Multiset (HasseDavenportMonicIrreduciblePolynomialAny K) //
    (s.map (fun q => q.1.natDegree)).sum = n}

/-- The normalized irreducible factorization of a monic polynomial. -/
def hasseDavenportIrreducibleFactorizationOfMonic
    (K : Type*) [Field K] (n : ℕ)
    (p : {p : Polynomial K // p.Monic ∧ p.natDegree = n}) :
    HasseDavenportIrreducibleFactorization K n := by
  let s := UniqueFactorizationMonoid.normalizedFactors p.1
  have hs : ∀ q ∈ s, q.Monic ∧ Irreducible q := by
    intro q hq
    exact ⟨(normalizedFactor_monic_irreducible_natDegree_pos p.2.1 hq).2.1,
      (normalizedFactor_monic_irreducible_natDegree_pos p.2.1 hq).1⟩
  let t : Multiset (HasseDavenportMonicIrreduciblePolynomialAny K) :=
    Multiset.pmap (fun q h => ⟨q, h⟩) s hs
  refine ⟨t, ?_⟩
  have hval : t.map (fun q => q.1) = s := by
    dsimp [t]
    rw [Multiset.map_pmap]
    exact (Multiset.pmap_eq_map _ id s hs).trans (Multiset.map_id s)
  calc
    (t.map (fun q => q.1.natDegree)).sum =
        (s.map Polynomial.natDegree).sum := by
      simpa [Function.comp_def] using
        congrArg (fun u : Multiset (Polynomial K) =>
          (u.map Polynomial.natDegree).sum) hval
    _ = p.1.natDegree := sum_natDegree_normalizedFactors_of_monic p.2.1
    _ = n := p.2.2

/-- Multiply a factor multiset to recover its monic polynomial. -/
def hasseDavenportMonicOfIrreducibleFactorization
    (K : Type*) [Field K] (n : ℕ)
    (s : HasseDavenportIrreducibleFactorization K n) :
    {p : Polynomial K // p.Monic ∧ p.natDegree = n} := by
  let p : Polynomial K := (s.1.map (fun q => q.1)).prod
  have hpmonic : p.Monic := by
    dsimp [p]
    exact monic_multiset_prod_of_monic s.1 (fun q => q.1)
      (fun q _hq => q.2.1)
  refine ⟨p, hpmonic, ?_⟩
  dsimp [p]
  have hmono : ∀ q ∈ s.1.map (fun q => q.1), q.Monic := by
    intro q hq
    obtain ⟨r, _hr, rfl⟩ := Multiset.mem_map.mp hq
    exact r.2.1
  rw [natDegree_multiset_prod_of_monic _ hmono, Multiset.map_map]
  exact s.2

theorem hasseDavenportIrreducibleFactorization_monic_left
    (K : Type*) [Field K] (n : ℕ)
    (p : {p : Polynomial K // p.Monic ∧ p.natDegree = n}) :
    hasseDavenportMonicOfIrreducibleFactorization K n
      (hasseDavenportIrreducibleFactorizationOfMonic K n p) = p := by
  apply Subtype.ext
  change ((hasseDavenportIrreducibleFactorizationOfMonic K n p).1.map
      (fun q => q.1)).prod = p.1
  have hmap :
      (hasseDavenportIrreducibleFactorizationOfMonic K n p).1.map
          (fun q => q.1) =
        UniqueFactorizationMonoid.normalizedFactors p.1 := by
    simp only [hasseDavenportIrreducibleFactorizationOfMonic]
    rw [Multiset.map_pmap, Multiset.pmap_eq_map]
    simp
  rw [hmap, UniqueFactorizationMonoid.prod_normalizedFactors_eq
    p.2.1.ne_zero, p.2.1.normalize_eq_self]

theorem hasseDavenportIrreducibleFactorization_monic_right
    (K : Type*) [Field K] (n : ℕ)
    (s : HasseDavenportIrreducibleFactorization K n) :
    hasseDavenportIrreducibleFactorizationOfMonic K n
      (hasseDavenportMonicOfIrreducibleFactorization K n s) = s := by
  apply Subtype.ext
  apply Multiset.map_injective Subtype.val_injective
  change (hasseDavenportIrreducibleFactorizationOfMonic K n
      (hasseDavenportMonicOfIrreducibleFactorization K n s)).1.map
        (fun q => q.1) = s.1.map (fun q => q.1)
  have hnorm : UniqueFactorizationMonoid.normalizedFactors
      ((s.1.map (fun q => q.1)).prod) = s.1.map (fun q => q.1) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq]
    · rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro q hq
      exact q.2.1.normalize_eq_self
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
      exact r.2.2
  simp only [hasseDavenportIrreducibleFactorizationOfMonic]
  rw [Multiset.map_pmap, Multiset.pmap_eq_map]
  simpa [hasseDavenportMonicOfIrreducibleFactorization] using hnorm

/-- Unique factorization as an equivalence between fixed-degree monic
polynomials and irreducible factor multisets. -/
def hasseDavenportMonicIrreducibleFactorizationEquiv
    (K : Type*) [Field K] (n : ℕ) :
    {p : Polynomial K // p.Monic ∧ p.natDegree = n} ≃
      HasseDavenportIrreducibleFactorization K n where
  toFun := hasseDavenportIrreducibleFactorizationOfMonic K n
  invFun := hasseDavenportMonicOfIrreducibleFactorization K n
  left_inv := hasseDavenportIrreducibleFactorization_monic_left K n
  right_inv := hasseDavenportIrreducibleFactorization_monic_right K n

noncomputable instance hasseDavenportIrreducibleFactorizationFintype
    (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    Fintype (HasseDavenportIrreducibleFactorization K n) :=
  Fintype.ofEquiv {p : Polynomial K // p.Monic ∧ p.natDegree = n}
    (hasseDavenportMonicIrreducibleFactorizationEquiv K n)

/-- Forget the degree index on a bounded monic irreducible polynomial. -/
def hasseDavenportIrreducibleAnyOfUpTo
    {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) :
    HasseDavenportMonicIrreduciblePolynomialAny K :=
  ⟨hasseDavenportIrreduciblePolynomial q,
    hasseDavenportIrreduciblePolynomial_monic q,
    hasseDavenportIrreduciblePolynomial_irreducible q⟩

@[simp] theorem hasseDavenportIrreducibleAnyOfUpTo_natDegree
    {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportIrreduciblePolynomialUpTo K N) :
    (hasseDavenportIrreducibleAnyOfUpTo q).1.natDegree =
      hasseDavenportIrreducibleDegree q :=
  hasseDavenportIrreduciblePolynomial_natDegree q

theorem hasseDavenportIrreducibleAnyOfUpTo_injective
    {K : Type*} [Field K] {N : ℕ} :
    Function.Injective
      (hasseDavenportIrreducibleAnyOfUpTo (K := K) (N := N)) := by
  rintro ⟨qd, q⟩ ⟨rd, r⟩ h
  have hpoly : q.1.1 = r.1.1 :=
    congrArg (fun z : HasseDavenportMonicIrreduciblePolynomialAny K => z.1) h
  have hd : qd = rd := by
    apply Fin.ext
    exact q.1.2.2.symm.trans
      ((congrArg Polynomial.natDegree hpoly).trans r.1.2.2)
  subst rd
  congr
  apply Subtype.ext
  apply Subtype.ext
  exact hpoly

/-- A valid cutoff-`N`, total-degree-`n` allocation in the Euler product. -/
def HasseDavenportIrreducibleAllocation
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) :=
  {l : HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ //
    l ∈ Finset.finsuppAntidiag
      (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N)) n ∧
    ∀ q, hasseDavenportIrreducibleDegree q ∣ l q}

/-- Regard a factor of a degree-`n` factorization as an irreducible in any
cutoff `N ≥ n`. -/
def hasseDavenportIrreducibleUpToOfFactor
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) (hnN : n ≤ N)
    (s : HasseDavenportIrreducibleFactorization K n)
    (q : HasseDavenportMonicIrreduciblePolynomialAny K) (hq : q ∈ s.1) :
    HasseDavenportIrreduciblePolynomialUpTo K N := by
  have hqn : q.1.natDegree ≤ n := by
    rw [← s.2]
    apply Multiset.le_sum_of_mem
    exact Multiset.mem_map.mpr ⟨q, hq, rfl⟩
  exact ⟨⟨q.1.natDegree, Nat.lt_succ_iff.mpr (hqn.trans hnN)⟩,
    ⟨⟨q.1, q.2.1, rfl⟩, q.2.2⟩⟩

@[simp] theorem hasseDavenportIrreducibleAnyOfUpTo_ofFactor
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) (hnN : n ≤ N)
    (s : HasseDavenportIrreducibleFactorization K n)
    (q : HasseDavenportMonicIrreduciblePolynomialAny K) (hq : q ∈ s.1) :
    hasseDavenportIrreducibleAnyOfUpTo
      (hasseDavenportIrreducibleUpToOfFactor K N n hnN s q hq) = q := by
  apply Subtype.ext
  rfl

theorem sum_hasseDavenportIrreducible_count_mul_degree
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) (hnN : n ≤ N)
    (s : HasseDavenportIrreducibleFactorization K n) :
    ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        s.1.count (hasseDavenportIrreducibleAnyOfUpTo q) *
          hasseDavenportIrreducibleDegree q = n := by
  let e : {q // q ∈ s.1.toFinset} →
      HasseDavenportIrreduciblePolynomialUpTo K N :=
    fun q => hasseDavenportIrreducibleUpToOfFactor K N n hnN s q.1
      (Multiset.mem_toFinset.mp q.2)
  have he : Function.Injective e := by
    intro q r h
    apply Subtype.ext
    have hany := congrArg hasseDavenportIrreducibleAnyOfUpTo h
    simpa [e] using hany
  let t : Finset (HasseDavenportIrreduciblePolynomialUpTo K N) :=
    s.1.toFinset.attach.image e
  calc
    ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        s.1.count (hasseDavenportIrreducibleAnyOfUpTo q) *
          hasseDavenportIrreducibleDegree q =
        ∑ q ∈ t,
          s.1.count (hasseDavenportIrreducibleAnyOfUpTo q) *
            hasseDavenportIrreducibleDegree q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ t)
      intro q _hq hqt
      have hnot : hasseDavenportIrreducibleAnyOfUpTo q ∉ s.1 := by
        intro hmem
        apply hqt
        apply Finset.mem_image.mpr
        refine ⟨⟨hasseDavenportIrreducibleAnyOfUpTo q, by simpa using hmem⟩,
          by simp, ?_⟩
        apply hasseDavenportIrreducibleAnyOfUpTo_injective
        simp [e]
      rw [Multiset.count_eq_zero.mpr hnot]
      simp
    _ = ∑ q ∈ s.1.toFinset,
        s.1.count q * q.1.natDegree := by
      dsimp [t]
      rw [Finset.sum_image he.injOn]
      exact Finset.sum_attach s.1.toFinset
        (fun q => s.1.count q * q.1.natDegree)
    _ = (s.1.map (fun q => q.1.natDegree)).sum := by
      rw [Finset.sum_multiset_map_count]
      simp [mul_comm]
    _ = n := s.2

/-- Convert a factor multiset to its degree allocation at a larger cutoff. -/
def hasseDavenportIrreducibleAllocationOfFactorization
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) (hnN : n ≤ N)
    (s : HasseDavenportIrreducibleFactorization K n) :
    HasseDavenportIrreducibleAllocation K N n := by
  let l : HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun q =>
      s.1.count (hasseDavenportIrreducibleAnyOfUpTo q) *
        hasseDavenportIrreducibleDegree q)
  refine ⟨l, ?_, ?_⟩
  · rw [Finset.mem_finsuppAntidiag]
    exact ⟨by simpa [l] using
      sum_hasseDavenportIrreducible_count_mul_degree K N n hnN s,
      Finset.subset_univ _⟩
  · intro q
    change hasseDavenportIrreducibleDegree q ∣
      s.1.count (hasseDavenportIrreducibleAnyOfUpTo q) *
        hasseDavenportIrreducibleDegree q
    exact dvd_mul_left _ _

/-- Place an arbitrary monic irreducible polynomial in a cutoff known to
contain its degree. -/
def hasseDavenportIrreducibleUpToOfAny
    {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportMonicIrreduciblePolynomialAny K)
    (hq : q.1.natDegree ≤ N) :
    HasseDavenportIrreduciblePolynomialUpTo K N :=
  ⟨⟨q.1.natDegree, Nat.lt_succ_iff.mpr hq⟩,
    ⟨⟨q.1, q.2.1, rfl⟩, q.2.2⟩⟩

@[simp] theorem hasseDavenportIrreducibleDegree_upToOfAny
    {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportMonicIrreduciblePolynomialAny K)
    (hq : q.1.natDegree ≤ N) :
    hasseDavenportIrreducibleDegree
      (hasseDavenportIrreducibleUpToOfAny q hq) = q.1.natDegree := rfl

@[simp] theorem hasseDavenportIrreducibleAnyOfUpTo_ofAny
    {K : Type*} [Field K] {N : ℕ}
    (q : HasseDavenportMonicIrreduciblePolynomialAny K)
    (hq : q.1.natDegree ≤ N) :
    hasseDavenportIrreducibleAnyOfUpTo
      (hasseDavenportIrreducibleUpToOfAny q hq) = q := by
  apply Subtype.ext
  rfl

/-- Expand an Euler allocation into the corresponding multiset of
irreducible factors. -/
def hasseDavenportIrreducibleFactorizationOfAllocation
    (K : Type*) [Field K] [Fintype K] (N n : ℕ)
    (l : HasseDavenportIrreducibleAllocation K N n) :
    HasseDavenportIrreducibleFactorization K n := by
  let s : Multiset (HasseDavenportMonicIrreduciblePolynomialAny K) :=
    ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
      Multiset.replicate
        (l.1 q / hasseDavenportIrreducibleDegree q)
        (hasseDavenportIrreducibleAnyOfUpTo q)
  refine ⟨s, ?_⟩
  have hsum :
      ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N, l.1 q = n :=
    (Finset.mem_finsuppAntidiag.mp l.2.1).1
  have hmapSum :
      s.map (fun q => q.1.natDegree) =
        ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
          (Multiset.replicate
            (l.1 q / hasseDavenportIrreducibleDegree q)
            (hasseDavenportIrreducibleAnyOfUpTo q)).map
              (fun r => r.1.natDegree) := by
    dsimp [s]
    exact map_sum (Multiset.mapAddMonoidHom (fun q => q.1.natDegree))
      (fun q : HasseDavenportIrreduciblePolynomialUpTo K N =>
        Multiset.replicate
          (l.1 q / hasseDavenportIrreducibleDegree q)
          (hasseDavenportIrreducibleAnyOfUpTo q)) Finset.univ
  calc
    (s.map (fun q => q.1.natDegree)).sum =
        ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
          (l.1 q / hasseDavenportIrreducibleDegree q) *
            hasseDavenportIrreducibleDegree q := by
      rw [hmapSum]
      change Multiset.sumAddMonoidHom
          (∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
            (Multiset.replicate
              (l.1 q / hasseDavenportIrreducibleDegree q)
              (hasseDavenportIrreducibleAnyOfUpTo q)).map
                (fun r => r.1.natDegree)) = _
      rw [map_sum Multiset.sumAddMonoidHom]
      simp [Multiset.map_replicate, mul_comm]
    _ = ∑ q : HasseDavenportIrreduciblePolynomialUpTo K N, l.1 q := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact Nat.div_mul_cancel (l.2.2 q)
    _ = n := hsum

theorem count_hasseDavenportIrreducibleFactorizationOfAllocation
    (K : Type*) [Field K] [Fintype K] (N n : ℕ)
    (l : HasseDavenportIrreducibleAllocation K N n)
    (q : HasseDavenportMonicIrreduciblePolynomialAny K) :
    (hasseDavenportIrreducibleFactorizationOfAllocation K N n l).1.count q =
      if hq : q.1.natDegree ≤ N then
        l.1 (hasseDavenportIrreducibleUpToOfAny q hq) / q.1.natDegree
      else 0 := by
  classical
  let countHom : Multiset (HasseDavenportMonicIrreduciblePolynomialAny K) →+ ℕ :=
    { toFun := fun m => Multiset.count q m
      map_zero' := Multiset.count_zero q
      map_add' := fun u v => Multiset.count_add q u v }
  change countHom
      (∑ r : HasseDavenportIrreduciblePolynomialUpTo K N,
        Multiset.replicate
          (l.1 r / hasseDavenportIrreducibleDegree r)
          (hasseDavenportIrreducibleAnyOfUpTo r)) = _
  rw [map_sum countHom]
  by_cases hq : q.1.natDegree ≤ N
  · rw [dif_pos hq]
    let q' : HasseDavenportIrreduciblePolynomialUpTo K N :=
      hasseDavenportIrreducibleUpToOfAny q hq
    rw [Finset.sum_eq_single q']
    · simp [countHom, q']
    · intro r _hr hrq
      change Multiset.count q
        (Multiset.replicate
          (l.1 r / hasseDavenportIrreducibleDegree r)
          (hasseDavenportIrreducibleAnyOfUpTo r)) = 0
      rw [Multiset.count_replicate, if_neg]
      intro h
      apply hrq
      apply hasseDavenportIrreducibleAnyOfUpTo_injective
      simpa [q'] using h
    · simp
  · rw [dif_neg hq]
    apply Finset.sum_eq_zero
    intro r _hr
    change Multiset.count q
      (Multiset.replicate
        (l.1 r / hasseDavenportIrreducibleDegree r)
        (hasseDavenportIrreducibleAnyOfUpTo r)) = 0
    rw [Multiset.count_replicate, if_neg]
    intro hr
    apply hq
    have hdeg := congrArg
      (fun z : HasseDavenportMonicIrreduciblePolynomialAny K => z.1.natDegree) hr
    have hdeg' : q.1.natDegree = hasseDavenportIrreducibleDegree r := by
      simpa only [hasseDavenportIrreducibleAnyOfUpTo_natDegree] using hdeg.symm
    rw [hdeg']
    exact Nat.le_of_lt_succ r.1.2

theorem hasseDavenportIrreducibleAllocation_factorization_left
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) (hnN : n ≤ N)
    (s : HasseDavenportIrreducibleFactorization K n) :
    hasseDavenportIrreducibleFactorizationOfAllocation K N n
      (hasseDavenportIrreducibleAllocationOfFactorization K N n hnN s) = s := by
  apply Subtype.ext
  apply Multiset.ext.mpr
  intro q
  rw [count_hasseDavenportIrreducibleFactorizationOfAllocation]
  by_cases hq : q ∈ s.1
  · have hdeg : q.1.natDegree ≤ N := by
      apply le_trans (show q.1.natDegree ≤ n by
        rw [← s.2]
        apply Multiset.le_sum_of_mem
        exact Multiset.mem_map.mpr ⟨q, hq, rfl⟩) hnN
    rw [dif_pos hdeg]
    change (s.1.count q * q.1.natDegree) / q.1.natDegree = s.1.count q
    rw [mul_comm, Nat.mul_div_cancel_left _
      (q.2.1.natDegree_pos_of_not_isUnit q.2.2.not_isUnit)]
  · have hcount : s.1.count q = 0 := Multiset.count_eq_zero.mpr hq
    split
    · change (s.1.count q * q.1.natDegree) / q.1.natDegree = s.1.count q
      rw [hcount]
      simp
    · exact hcount.symm

theorem hasseDavenportIrreducibleAllocation_factorization_right
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) (hnN : n ≤ N)
    (l : HasseDavenportIrreducibleAllocation K N n) :
    hasseDavenportIrreducibleAllocationOfFactorization K N n hnN
      (hasseDavenportIrreducibleFactorizationOfAllocation K N n l) = l := by
  apply Subtype.ext
  apply Finsupp.ext
  intro q
  change (hasseDavenportIrreducibleFactorizationOfAllocation K N n l).1.count
      (hasseDavenportIrreducibleAnyOfUpTo q) *
        hasseDavenportIrreducibleDegree q = l.1 q
  have hle : (hasseDavenportIrreducibleAnyOfUpTo q).1.natDegree ≤ N := by
    simpa using Nat.le_of_lt_succ q.1.2
  rw [count_hasseDavenportIrreducibleFactorizationOfAllocation,
    dif_pos hle]
  have heq : hasseDavenportIrreducibleUpToOfAny
      (hasseDavenportIrreducibleAnyOfUpTo q)
      hle = q := by
    apply hasseDavenportIrreducibleAnyOfUpTo_injective
    simp
  rw [heq, hasseDavenportIrreducibleAnyOfUpTo_natDegree]
  exact Nat.div_mul_cancel (l.2.2 q)

/-- Factor multisets and valid cutoff allocations are equivalent whenever
the cutoff contains the total degree. -/
def hasseDavenportIrreducibleFactorizationAllocationEquiv
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) (hnN : n ≤ N) :
    HasseDavenportIrreducibleFactorization K n ≃
      HasseDavenportIrreducibleAllocation K N n where
  toFun := hasseDavenportIrreducibleAllocationOfFactorization K N n hnN
  invFun := hasseDavenportIrreducibleFactorizationOfAllocation K N n
  left_inv := hasseDavenportIrreducibleAllocation_factorization_left K N n hnN
  right_inv := hasseDavenportIrreducibleAllocation_factorization_right K N n hnN

/-- The finite set of valid divisible allocations. -/
def hasseDavenportIrreducibleAllocationFinset
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) :
    Finset (HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ) :=
  (Finset.finsuppAntidiag
    (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N)) n).filter
      (fun l => ∀ q, hasseDavenportIrreducibleDegree q ∣ l q)

def hasseDavenportIrreducibleAllocationSubtypeEquiv
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) :
    {l // l ∈ hasseDavenportIrreducibleAllocationFinset K N n} ≃
      HasseDavenportIrreducibleAllocation K N n where
  toFun l := ⟨l.1, (Finset.mem_filter.mp l.2).1,
    (Finset.mem_filter.mp l.2).2⟩
  invFun l := ⟨l.1, Finset.mem_filter.mpr ⟨l.2.1, l.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance hasseDavenportIrreducibleAllocationFintype
    (K : Type*) [Field K] [Fintype K] (N n : ℕ) :
    Fintype (HasseDavenportIrreducibleAllocation K N n) :=
  Fintype.ofEquiv
    {l // l ∈ hasseDavenportIrreducibleAllocationFinset K N n}
    (hasseDavenportIrreducibleAllocationSubtypeEquiv K N n)

/-- The product weight attached to a valid irreducible allocation. -/
def hasseDavenportIrreducibleAllocationWeight
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ)
    (l : HasseDavenportIrreducibleAllocation K N n) : ℂ :=
  ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
    hasseDavenportIrreducibleWeight χ ψ q ^
      (l.1 q / hasseDavenportIrreducibleDegree q)

theorem hasseDavenportIrreducibleEulerProductTerm_eq_weight
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N : ℕ)
    (l : HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ)
    (hl : ∀ q, hasseDavenportIrreducibleDegree q ∣ l q) :
    (∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        if hasseDavenportIrreducibleDegree q ∣ l q then
          hasseDavenportIrreducibleWeight χ ψ q ^
            (l q / hasseDavenportIrreducibleDegree q)
        else 0) =
      ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        hasseDavenportIrreducibleWeight χ ψ q ^
          (l q / hasseDavenportIrreducibleDegree q) := by
  apply Finset.prod_congr rfl
  intro q _hq
  rw [if_pos (hl q)]

theorem hasseDavenportIrreducibleEulerProductTerm_eq_zero
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N : ℕ)
    (l : HasseDavenportIrreduciblePolynomialUpTo K N →₀ ℕ)
    (hl : ¬ ∀ q, hasseDavenportIrreducibleDegree q ∣ l q) :
    (∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
        if hasseDavenportIrreducibleDegree q ∣ l q then
          hasseDavenportIrreducibleWeight χ ψ q ^
            (l q / hasseDavenportIrreducibleDegree q)
        else 0) = 0 := by
  push Not at hl
  obtain ⟨q, hq⟩ := hl
  apply Finset.prod_eq_zero (Finset.mem_univ q)
  rw [if_neg hq]

theorem sum_hasseDavenportIrreducibleAllocationWeight_eq_finset
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ) :
    (∑ l : HasseDavenportIrreducibleAllocation K N n,
        hasseDavenportIrreducibleAllocationWeight K χ ψ N n l) =
      ∑ l ∈ hasseDavenportIrreducibleAllocationFinset K N n,
        ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
          hasseDavenportIrreducibleWeight χ ψ q ^
            (l q / hasseDavenportIrreducibleDegree q) := by
  symm
  calc
    (∑ l ∈ hasseDavenportIrreducibleAllocationFinset K N n,
        ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
          hasseDavenportIrreducibleWeight χ ψ q ^
            (l q / hasseDavenportIrreducibleDegree q)) =
        ∑ l : {l // l ∈ hasseDavenportIrreducibleAllocationFinset K N n},
          ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
            hasseDavenportIrreducibleWeight χ ψ q ^
              (l.1 q / hasseDavenportIrreducibleDegree q) := by
      apply Finset.sum_subtype
      intro l
      rfl
    _ = ∑ l : HasseDavenportIrreducibleAllocation K N n,
        hasseDavenportIrreducibleAllocationWeight K χ ψ N n l := by
      apply Fintype.sum_equiv
        (hasseDavenportIrreducibleAllocationSubtypeEquiv K N n)
      intro l
      rfl

/-- The bounded Euler coefficient is the sum over valid allocations. -/
theorem hasseDavenportIrreducibleEulerCoefficient_eq_allocationSum
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ) :
    hasseDavenportIrreducibleEulerCoefficient K χ ψ N n =
      ∑ l : HasseDavenportIrreducibleAllocation K N n,
        hasseDavenportIrreducibleAllocationWeight K χ ψ N n l := by
  rw [hasseDavenportIrreducibleEulerCoefficient_eq_sum_allocations]
  rw [sum_hasseDavenportIrreducibleAllocationWeight_eq_finset K χ ψ N n]
  let s := Finset.finsuppAntidiag
    (Finset.univ : Finset (HasseDavenportIrreduciblePolynomialUpTo K N)) n
  let t := hasseDavenportIrreducibleAllocationFinset K N n
  calc
    (∑ l ∈ s,
        ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
          if hasseDavenportIrreducibleDegree q ∣ l q then
            hasseDavenportIrreducibleWeight χ ψ q ^
              (l q / hasseDavenportIrreducibleDegree q)
          else 0) =
        ∑ l ∈ t,
          ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
            if hasseDavenportIrreducibleDegree q ∣ l q then
              hasseDavenportIrreducibleWeight χ ψ q ^
                (l q / hasseDavenportIrreducibleDegree q)
            else 0 := by
      symm
      apply Finset.sum_subset
      · exact Finset.filter_subset _ _
      · intro l hls hlt
        apply hasseDavenportIrreducibleEulerProductTerm_eq_zero K χ ψ N l
        intro hall
        apply hlt
        exact Finset.mem_filter.mpr ⟨hls, hall⟩
    _ = ∑ l ∈ t,
        ∏ q : HasseDavenportIrreduciblePolynomialUpTo K N,
          hasseDavenportIrreducibleWeight χ ψ q ^
            (l q / hasseDavenportIrreducibleDegree q) := by
      apply Finset.sum_congr rfl
      intro l hlt
      apply hasseDavenportIrreducibleEulerProductTerm_eq_weight K χ ψ N l
      exact (Finset.mem_filter.mp hlt).2

/-- Product of a mapped finite sum of replicated multisets. -/
theorem hasseDavenport_prod_map_sum_replicate
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

/-- The multiplicative weight of an irreducible factor multiset. -/
def hasseDavenportIrreducibleFactorizationWeight
    (K : Type*) [Field K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (n : ℕ)
    (s : HasseDavenportIrreducibleFactorization K n) : ℂ :=
  (s.1.map (fun q => hasseDavenportMonicWeight χ ψ q.1)).prod

theorem hasseDavenportIrreducibleFactorizationWeight_ofAllocation
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ)
    (l : HasseDavenportIrreducibleAllocation K N n) :
    hasseDavenportIrreducibleFactorizationWeight K χ ψ n
        (hasseDavenportIrreducibleFactorizationOfAllocation K N n l) =
      hasseDavenportIrreducibleAllocationWeight K χ ψ N n l := by
  unfold hasseDavenportIrreducibleFactorizationWeight
    hasseDavenportIrreducibleAllocationWeight
  change (((∑ q : HasseDavenportIrreduciblePolynomialUpTo K N,
      Multiset.replicate
        (l.1 q / hasseDavenportIrreducibleDegree q)
        (hasseDavenportIrreducibleAnyOfUpTo q)).map
          (fun q => hasseDavenportMonicWeight χ ψ q.1)).prod) = _
  simpa [hasseDavenportIrreducibleWeight,
    hasseDavenportIrreducibleAnyOfUpTo,
    hasseDavenportIrreduciblePolynomial] using
    hasseDavenport_prod_map_sum_replicate Finset.univ
      (fun q : HasseDavenportIrreduciblePolynomialUpTo K N =>
        l.1 q / hasseDavenportIrreducibleDegree q)
      (fun q => hasseDavenportIrreducibleAnyOfUpTo q)
      (fun q => hasseDavenportMonicWeight χ ψ q.1)

/-- The bounded Euler coefficient is the factor-multiset weight sum once the
cutoff contains the coefficient degree. -/
theorem hasseDavenportIrreducibleEulerCoefficient_eq_factorizationSum
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ) (hnN : n ≤ N) :
    hasseDavenportIrreducibleEulerCoefficient K χ ψ N n =
      ∑ s : HasseDavenportIrreducibleFactorization K n,
        hasseDavenportIrreducibleFactorizationWeight K χ ψ n s := by
  rw [hasseDavenportIrreducibleEulerCoefficient_eq_allocationSum]
  symm
  apply Fintype.sum_equiv
    (hasseDavenportIrreducibleFactorizationAllocationEquiv K N n hnN)
  intro s
  calc
    hasseDavenportIrreducibleFactorizationWeight K χ ψ n s =
        hasseDavenportIrreducibleFactorizationWeight K χ ψ n
          (hasseDavenportIrreducibleFactorizationOfAllocation K N n
            (hasseDavenportIrreducibleFactorizationAllocationEquiv K N n hnN s)) := by
      congr 1
      exact (hasseDavenportIrreducibleAllocation_factorization_left K N n hnN s).symm
    _ = hasseDavenportIrreducibleAllocationWeight K χ ψ N n
          (hasseDavenportIrreducibleFactorizationAllocationEquiv K N n hnN s) :=
      hasseDavenportIrreducibleFactorizationWeight_ofAllocation K χ ψ N n _

theorem hasseDavenportIrreducibleFactorizationOfMonic_map_val
    (K : Type*) [Field K] (n : ℕ)
    (p : {p : Polynomial K // p.Monic ∧ p.natDegree = n}) :
    (hasseDavenportIrreducibleFactorizationOfMonic K n p).1.map
        (fun q => q.1) =
      UniqueFactorizationMonoid.normalizedFactors p.1 := by
  simp only [hasseDavenportIrreducibleFactorizationOfMonic]
  rw [Multiset.map_pmap, Multiset.pmap_eq_map]
  simp

theorem hasseDavenportMonicWeight_eq_irreducibleFactorizationWeight
    (K : Type*) [Field K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (n : ℕ)
    (p : {p : Polynomial K // p.Monic ∧ p.natDegree = n}) :
    hasseDavenportMonicWeight χ ψ p.1 =
      hasseDavenportIrreducibleFactorizationWeight K χ ψ n
        (hasseDavenportIrreducibleFactorizationOfMonic K n p) := by
  rw [hasseDavenportMonicWeight_eq_prod_normalizedFactors χ ψ p.2.1]
  unfold hasseDavenportIrreducibleFactorizationWeight
  rw [← hasseDavenportIrreducibleFactorizationOfMonic_map_val K n p,
    Multiset.map_map]
  rfl

theorem hasseDavenportMonicSum_eq_irreducibleFactorizationSum
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (n : ℕ) :
    hasseDavenportMonicSum K χ ψ n =
      ∑ s : HasseDavenportIrreducibleFactorization K n,
        hasseDavenportIrreducibleFactorizationWeight K χ ψ n s := by
  rw [hasseDavenportMonicSum]
  apply Fintype.sum_equiv
    (hasseDavenportMonicIrreducibleFactorizationEquiv K n)
  intro p
  exact hasseDavenportMonicWeight_eq_irreducibleFactorizationWeight K χ ψ n p

/-- The bounded irreducible Euler product has exactly the genuine monic
Hasse--Davenport coefficient in every degree below its cutoff. -/
theorem hasseDavenportIrreducibleEulerCoefficient_eq_monicSum
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (N n : ℕ) (hnN : n ≤ N) :
    hasseDavenportIrreducibleEulerCoefficient K χ ψ N n =
      hasseDavenportMonicSum K χ ψ n := by
  rw [hasseDavenportIrreducibleEulerCoefficient_eq_factorizationSum
    K χ ψ N n hnN,
    hasseDavenportMonicSum_eq_irreducibleFactorizationSum K χ ψ n]

namespace HasseDavenportLogDerivativeRecurrence

/-- The signed-power conclusion only uses the recurrence through the target
index. This truncated form is suited to a finite Euler product. -/
theorem signedPower_of_forall_le
    (A B : ℕ → ℂ) (G : ℂ)
    (hA0 : A 0 = 1) (hA1 : A 1 = G)
    (hAzero : ∀ m : ℕ, 2 ≤ m → A m = 0)
    (n : ℕ)
    (hrec : ∀ m ≤ n, (m + 1 : ℂ) * A (m + 1) =
      ∑ k ∈ Finset.range (m + 1), B (k + 1) * A (m - k)) :
    B (n + 1) = (-1 : ℂ) ^ n * G ^ (n + 1) := by
  induction n with
  | zero =>
      simpa [hA0, hA1] using (hrec 0 (by omega)).symm
  | succ n ih =>
      have hearly :
          ∑ k ∈ Finset.range n, B (k + 1) * A (n + 1 - k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        rw [hAzero (n + 1 - k) (by omega), mul_zero]
      have h := hrec (n + 1) (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hearly] at h
      have hsub1 : n + 1 - n = 1 := by omega
      have hsub0 : n + 1 - (n + 1) = 0 := by omega
      rw [hAzero (n + 2) (by omega), hsub1, hsub0, hA1, hA0] at h
      simp only [mul_zero, zero_add, mul_one] at h
      rw [ih (fun m hm => hrec m (by omega))] at h
      rw [pow_succ, pow_succ]
      linear_combination -h

end HasseDavenportLogDerivativeRecurrence

/-- Below the cutoff, the closed-point coefficients of the irreducible Euler
product are the signed powers dictated by Hasse--Davenport. -/
theorem hasseDavenportIrreducibleClosedPointCoefficient_eq_signedGaussPower
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (hχ : χ ≠ 1)
    (N n : ℕ) (hnN : n + 1 ≤ N) :
    hasseDavenportIrreducibleClosedPointCoefficient K χ ψ N (n + 1) =
      (-1 : ℂ) ^ n * gaussSum χ ψ ^ (n + 1) := by
  apply HasseDavenportLogDerivativeRecurrence.signedPower_of_forall_le
    (hasseDavenportMonicSum K χ ψ)
    (hasseDavenportIrreducibleClosedPointCoefficient K χ ψ N)
    (gaussSum χ ψ)
  · exact hasseDavenportMonicSum_zero K χ ψ
  · exact hasseDavenportMonicSum_one K χ ψ
  · exact hasseDavenportMonicSum_eq_zero_of_two_le K χ ψ hχ
  · intro m hm
    have hrec := hasseDavenportIrreducibleEulerRecurrence K χ ψ N m
    calc
      (m + 1 : ℂ) * hasseDavenportMonicSum K χ ψ (m + 1) =
          (m + 1 : ℂ) *
            hasseDavenportIrreducibleEulerCoefficient K χ ψ N (m + 1) := by
        rw [hasseDavenportIrreducibleEulerCoefficient_eq_monicSum
          K χ ψ N (m + 1) (by omega)]
      _ = ∑ k ∈ Finset.range (m + 1),
          hasseDavenportIrreducibleClosedPointCoefficient K χ ψ N (k + 1) *
            hasseDavenportIrreducibleEulerCoefficient K χ ψ N (m - k) := hrec
      _ = ∑ k ∈ Finset.range (m + 1),
          hasseDavenportIrreducibleClosedPointCoefficient K χ ψ N (k + 1) *
            hasseDavenportMonicSum K χ ψ (m - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hasseDavenportIrreducibleEulerCoefficient_eq_monicSum
          K χ ψ N (m - k) (by omega)]

/-- The explicit degree-stratified irreducible sum is the signed Gauss-sum
power. This is the polynomial closed-point side of Hasse--Davenport. -/
theorem hasseDavenportIrreducibleDegreeSum_eq_signedGaussPower
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (hχ : χ ≠ 1)
    (N n : ℕ) (hnN : n + 1 ≤ N) :
    (∑ d : Fin (N + 1), if d.1 ∣ n + 1 then
        (d.1 : ℂ) *
          ∑ q : HasseDavenportMonicIrreduciblePolynomial K d.1,
            hasseDavenportMonicWeight χ ψ q.1.1 ^ ((n + 1) / d.1)
      else 0) =
      (-1 : ℂ) ^ n * gaussSum χ ψ ^ (n + 1) := by
  rw [← hasseDavenportIrreducibleClosedPointCoefficient_eq_degree_sum
    K χ ψ N n]
  exact hasseDavenportIrreducibleClosedPointCoefficient_eq_signedGaussPower
    K χ ψ hχ N n hnN

end Tao2026

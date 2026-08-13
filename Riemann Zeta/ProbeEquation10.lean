import RiemannZeta.GuthMaynard.KloostermanLocalEuler
import Mathlib.RingTheory.PowerSeries.Derivative

open Polynomial Classical
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

noncomputable section

noncomputable def harcosPrimeUpToOfFactorAt
    (p N d : ℕ) [Fact p.Prime] (hdN : d ≤ N)
    (s : HarcosFactorization p d)
    (q : HarcosIrreducibleMonic p) (hq : q ∈ s.1) :
    HarcosPrimeUpTo p N :=
  ⟨q, le_trans (by
      rw [← s.2]
      apply Multiset.le_sum_of_mem
      exact Multiset.mem_map.mpr ⟨q, hq, rfl⟩) hdN⟩

theorem sum_harcosPrimeUpTo_count_mul_degree_at
    (p N d : ℕ) [Fact p.Prime] (hdN : d ≤ N)
    (s : HarcosFactorization p d) :
    ∑ q : HarcosPrimeUpTo p N,
        s.1.count q.1 * q.1.1.natDegree = d := by
  let e : {q // q ∈ s.1.toFinset} → HarcosPrimeUpTo p N :=
    fun q ↦ harcosPrimeUpToOfFactorAt p N d hdN s q.1
      (Multiset.mem_toFinset.mp q.2)
  have he : Function.Injective e := by
    intro q r h
    apply Subtype.ext
    exact congrArg (fun z : HarcosPrimeUpTo p N ↦ z.1) h
  let t : Finset (HarcosPrimeUpTo p N) :=
    s.1.toFinset.attach.image e
  calc
    ∑ q : HarcosPrimeUpTo p N,
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
    _ = d := s.2

def HarcosEulerAllocationAt
    (p N d : ℕ) [Fact p.Prime] :=
  {l : HarcosPrimeUpTo p N →₀ ℕ //
    l ∈ Finset.finsuppAntidiag Finset.univ d ∧
      ∀ q, q.1.1.natDegree ∣ l q}

noncomputable def harcosEulerAllocationAtOfFactorization
    (p N d : ℕ) [Fact p.Prime] (hdN : d ≤ N)
    (s : HarcosFactorization p d) :
    HarcosEulerAllocationAt p N d := by
  let l : HarcosPrimeUpTo p N →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm
      (fun q ↦ s.1.count q.1 * q.1.1.natDegree)
  refine ⟨l, ?_, ?_⟩
  · rw [Finset.mem_finsuppAntidiag]
    exact ⟨by simpa [l] using
      sum_harcosPrimeUpTo_count_mul_degree_at p N d hdN s,
      Finset.subset_univ _⟩
  · intro q
    change q.1.1.natDegree ∣ s.1.count q.1 * q.1.1.natDegree
    exact dvd_mul_left _ _

noncomputable def harcosFactorizationOfEulerAllocationAt
    (p N d : ℕ) [Fact p.Prime]
    (l : HarcosEulerAllocationAt p N d) :
    HarcosFactorization p d := by
  let s : Multiset (HarcosIrreducibleMonic p) :=
    ∑ q : HarcosPrimeUpTo p N,
      Multiset.replicate (l.1 q / q.1.1.natDegree) q.1
  refine ⟨s, ?_⟩
  have hsum : ∑ q : HarcosPrimeUpTo p N, l.1 q = d :=
    (Finset.mem_finsuppAntidiag.mp l.2.1).1
  have hmapSum :
      s.map (fun q ↦ q.1.natDegree) =
        ∑ q : HarcosPrimeUpTo p N,
          (Multiset.replicate (l.1 q / q.1.1.natDegree) q.1).map
            (fun r ↦ r.1.natDegree) := by
    dsimp [s]
    exact map_sum (Multiset.mapAddMonoidHom (fun q ↦ q.1.natDegree))
      (fun q : HarcosPrimeUpTo p N ↦
        Multiset.replicate (l.1 q / q.1.1.natDegree) q.1) Finset.univ
  calc
    (s.map (fun q ↦ q.1.natDegree)).sum =
        ∑ q : HarcosPrimeUpTo p N,
          (l.1 q / q.1.1.natDegree) * q.1.1.natDegree := by
      rw [hmapSum]
      change Multiset.sumAddMonoidHom
          (∑ q : HarcosPrimeUpTo p N,
            (Multiset.replicate (l.1 q / q.1.1.natDegree) q.1).map
              (fun r ↦ r.1.natDegree)) = _
      rw [map_sum Multiset.sumAddMonoidHom]
      simp [Multiset.map_replicate, mul_comm]
    _ = ∑ q : HarcosPrimeUpTo p N, l.1 q := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact Nat.div_mul_cancel (l.2.2 q)
    _ = d := hsum

theorem count_harcosFactorizationOfEulerAllocationAt
    (p N d : ℕ) [Fact p.Prime]
    (l : HarcosEulerAllocationAt p N d)
    (q : HarcosIrreducibleMonic p) :
    (harcosFactorizationOfEulerAllocationAt p N d l).1.count q =
      if hq : q.1.natDegree ≤ N then
        l.1 (⟨q, hq⟩ : HarcosPrimeUpTo p N) / q.1.natDegree
      else 0 := by
  classical
  let countHom : Multiset (HarcosIrreducibleMonic p) →+ ℕ :=
    { toFun := fun m ↦ Multiset.count q m
      map_zero' := Multiset.count_zero q
      map_add' := fun u v ↦ Multiset.count_add q u v }
  change countHom
      (∑ r : HarcosPrimeUpTo p N,
        Multiset.replicate (l.1 r / r.1.1.natDegree) r.1) = _
  rw [map_sum countHom]
  by_cases hq : q.1.natDegree ≤ N
  · rw [dif_pos hq]
    let q' : HarcosPrimeUpTo p N := ⟨q, hq⟩
    rw [Finset.sum_eq_single q']
    · simp [countHom, q']
    · intro r _hr hrq
      change Multiset.count q
        (Multiset.replicate (l.1 r / r.1.1.natDegree) r.1) = 0
      rw [Multiset.count_replicate, if_neg]
      intro h
      apply hrq
      exact Subtype.ext h
    · simp
  · rw [dif_neg hq]
    apply Finset.sum_eq_zero
    intro r _hr
    change Multiset.count q
      (Multiset.replicate (l.1 r / r.1.1.natDegree) r.1) = 0
    rw [Multiset.count_replicate, if_neg]
    intro hr
    apply hq
    simpa [hr] using r.2

theorem harcosEulerAllocationAt_factorization_left
    (p N d : ℕ) [Fact p.Prime] (hdN : d ≤ N)
    (s : HarcosFactorization p d) :
    harcosFactorizationOfEulerAllocationAt p N d
      (harcosEulerAllocationAtOfFactorization p N d hdN s) = s := by
  apply Subtype.ext
  apply Multiset.ext.mpr
  intro q
  rw [count_harcosFactorizationOfEulerAllocationAt]
  by_cases hq : q ∈ s.1
  · have hdeg : q.1.natDegree ≤ N := le_trans (by
      rw [← s.2]
      apply Multiset.le_sum_of_mem
      exact Multiset.mem_map.mpr ⟨q, hq, rfl⟩) hdN
    rw [dif_pos hdeg]
    change (s.1.count q * q.1.natDegree) / q.1.natDegree = s.1.count q
    rw [mul_comm, Nat.mul_div_cancel_left _
      (harcosPrimeUpTo_degree_pos p N ⟨q, hdeg⟩)]
  · have hcount : s.1.count q = 0 := Multiset.count_eq_zero.mpr hq
    split
    · change (s.1.count q * q.1.natDegree) / q.1.natDegree = s.1.count q
      rw [hcount]
      simp
    · exact hcount.symm

theorem harcosEulerAllocationAt_factorization_right
    (p N d : ℕ) [Fact p.Prime] (hdN : d ≤ N)
    (l : HarcosEulerAllocationAt p N d) :
    harcosEulerAllocationAtOfFactorization p N d hdN
      (harcosFactorizationOfEulerAllocationAt p N d l) = l := by
  apply Subtype.ext
  apply Finsupp.ext
  intro q
  change (harcosFactorizationOfEulerAllocationAt p N d l).1.count q.1 *
      q.1.1.natDegree = l.1 q
  rw [count_harcosFactorizationOfEulerAllocationAt, dif_pos q.2]
  exact Nat.div_mul_cancel (l.2.2 q)

def harcosEulerAllocationAtEquiv
    (p N d : ℕ) [Fact p.Prime] (hdN : d ≤ N) :
    HarcosFactorization p d ≃ HarcosEulerAllocationAt p N d where
  toFun := harcosEulerAllocationAtOfFactorization p N d hdN
  invFun := harcosFactorizationOfEulerAllocationAt p N d
  left_inv := harcosEulerAllocationAt_factorization_left p N d hdN
  right_inv := harcosEulerAllocationAt_factorization_right p N d hdN

noncomputable def harcosEulerAllocationAtWeight
    (p N d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (l : HarcosEulerAllocationAt p N d) : ℂ :=
  ∏ q : HarcosPrimeUpTo p N,
    harcosEtaPolynomial p a b q.1.1 ^
      (l.1 q / q.1.1.natDegree)

theorem harcosFactorizationWeight_ofEulerAllocationAt
    (p N d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (l : HarcosEulerAllocationAt p N d) :
    harcosFactorizationWeight p d a b
        (harcosFactorizationOfEulerAllocationAt p N d l) =
      harcosEulerAllocationAtWeight p N d a b l := by
  unfold harcosFactorizationWeight harcosEulerAllocationAtWeight
  change (((∑ q : HarcosPrimeUpTo p N,
      Multiset.replicate (l.1 q / q.1.1.natDegree) q.1).map
        (fun q ↦ harcosEtaPolynomial p a b q.1)).prod) = _
  exact prod_map_sum_replicate Finset.univ
    (fun q : HarcosPrimeUpTo p N ↦ l.1 q / q.1.1.natDegree)
    (fun q ↦ q.1)
    (fun q ↦ harcosEtaPolynomial p a b q.1)

def harcosEulerAllocationAtFinset
    (p N d : ℕ) [Fact p.Prime] :
    Finset (HarcosPrimeUpTo p N →₀ ℕ) :=
  (Finset.finsuppAntidiag
    (Finset.univ : Finset (HarcosPrimeUpTo p N)) d).filter
      (fun l ↦ ∀ q, q.1.1.natDegree ∣ l q)

def harcosEulerAllocationAtSubtypeEquiv
    (p N d : ℕ) [Fact p.Prime] :
    {l // l ∈ harcosEulerAllocationAtFinset p N d} ≃
      HarcosEulerAllocationAt p N d where
  toFun l := ⟨l.1, (Finset.mem_filter.mp l.2).1,
    (Finset.mem_filter.mp l.2).2⟩
  invFun l := ⟨l.1, Finset.mem_filter.mpr ⟨l.2.1, l.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance harcosEulerAllocationAtFintype
    (p N d : ℕ) [Fact p.Prime] :
    Fintype (HarcosEulerAllocationAt p N d) :=
  Fintype.ofEquiv {l // l ∈ harcosEulerAllocationAtFinset p N d}
    (harcosEulerAllocationAtSubtypeEquiv p N d)

theorem sum_harcosEulerAllocationAtWeight_eq_finset
    (p N d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    (∑ l : HarcosEulerAllocationAt p N d,
        harcosEulerAllocationAtWeight p N d a b l) =
      ∑ l ∈ harcosEulerAllocationAtFinset p N d,
        ∏ q : HarcosPrimeUpTo p N,
          harcosEtaPolynomial p a b q.1.1 ^
            (l q / q.1.1.natDegree) := by
  symm
  calc
    (∑ l ∈ harcosEulerAllocationAtFinset p N d,
        ∏ q : HarcosPrimeUpTo p N,
          harcosEtaPolynomial p a b q.1.1 ^
            (l q / q.1.1.natDegree)) =
        ∑ l : {l // l ∈ harcosEulerAllocationAtFinset p N d},
          ∏ q : HarcosPrimeUpTo p N,
            harcosEtaPolynomial p a b q.1.1 ^
              (l.1 q / q.1.1.natDegree) := by
      apply Finset.sum_subtype
      intro l
      rfl
    _ = ∑ l : HarcosEulerAllocationAt p N d,
        harcosEulerAllocationAtWeight p N d a b l := by
      apply Fintype.sum_equiv
        (harcosEulerAllocationAtSubtypeEquiv p N d)
      intro l
      rfl

theorem coeff_harcosFiniteEulerProduct_raw_at
    (p N d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    PowerSeries.coeff d (harcosFiniteEulerProduct p N a b) =
      ∑ l ∈ Finset.finsuppAntidiag
          (Finset.univ : Finset (HarcosPrimeUpTo p N)) d,
        ∏ q : HarcosPrimeUpTo p N,
          if q.1.1.natDegree ∣ l q then
            harcosEtaPolynomial p a b q.1.1 ^
              (l q / q.1.1.natDegree)
          else 0 := by
  unfold harcosFiniteEulerProduct
  rw [show (∏ q : HarcosPrimeUpTo p N,
      harcosPrimeGeometricSeries p N a b q) =
      ∏ q ∈ (Finset.univ : Finset (HarcosPrimeUpTo p N)),
        harcosPrimeGeometricSeries p N a b q by simp]
  rw [PowerSeries.coeff_prod]
  simp only [coeff_harcosPrimeGeometricSeries]

theorem coeff_harcosFiniteEulerProduct_eq_allocationAtSum
    (p N d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    PowerSeries.coeff d (harcosFiniteEulerProduct p N a b) =
      ∑ l : HarcosEulerAllocationAt p N d,
        harcosEulerAllocationAtWeight p N d a b l := by
  rw [coeff_harcosFiniteEulerProduct_raw_at]
  rw [sum_harcosEulerAllocationAtWeight_eq_finset p N d]
  let s := Finset.finsuppAntidiag
    (Finset.univ : Finset (HarcosPrimeUpTo p N)) d
  let t := harcosEulerAllocationAtFinset p N d
  calc
    (∑ l ∈ s,
        ∏ q : HarcosPrimeUpTo p N,
          if q.1.1.natDegree ∣ l q then
            harcosEtaPolynomial p a b q.1.1 ^
              (l q / q.1.1.natDegree)
          else 0) =
        ∑ l ∈ t,
          ∏ q : HarcosPrimeUpTo p N,
            if q.1.1.natDegree ∣ l q then
              harcosEtaPolynomial p a b q.1.1 ^
                (l q / q.1.1.natDegree)
            else 0 := by
      symm
      apply Finset.sum_subset
      · exact Finset.filter_subset _ _
      · intro l hls hlt
        apply harcosEulerProductTerm_eq_zero p N a b l
        intro hall
        apply hlt
        exact Finset.mem_filter.mpr ⟨hls, hall⟩
    _ = ∑ l ∈ t,
        ∏ q : HarcosPrimeUpTo p N,
          harcosEtaPolynomial p a b q.1.1 ^
            (l q / q.1.1.natDegree) := by
      apply Finset.sum_congr rfl
      intro l hlt
      apply harcosEulerProductTerm_eq_weight p N a b l
      exact (Finset.mem_filter.mp hlt).2

theorem harcosEquationNine_truncated
    (p N d : ℕ) [NeZero p] [Fact p.Prime] (hdN : d ≤ N)
    (a b : ZMod p) :
    PowerSeries.coeff d (harcosFiniteEulerProduct p N a b) =
      PowerSeries.coeff d (harcosLSeries p a b) := by
  rw [coeff_harcosFiniteEulerProduct_eq_allocationAtSum p N d]
  rw [show (∑ l : HarcosEulerAllocationAt p N d,
      harcosEulerAllocationAtWeight p N d a b l) =
      ∑ s : HarcosFactorization p d,
        harcosFactorizationWeight p d a b s by
    symm
    apply Fintype.sum_equiv (harcosEulerAllocationAtEquiv p N d hdN)
    intro s
    calc
      harcosFactorizationWeight p d a b s =
          harcosFactorizationWeight p d a b
            (harcosFactorizationOfEulerAllocationAt p N d
              (harcosEulerAllocationAtEquiv p N d hdN s)) := by
        congr 1
        exact (harcosEulerAllocationAt_factorization_left p N d hdN s).symm
      _ = harcosEulerAllocationAtWeight p N d a b
            (harcosEulerAllocationAtEquiv p N d hdN s) :=
        harcosFactorizationWeight_ofEulerAllocationAt p N d a b _]
  rw [← harcosEtaDegreeSum_eq_factorizationSum]
  simp [harcosLSeries]

theorem coeff_monomial_mul_nat
    (d j : ℕ) (c : ℂ) (f : PowerSeries ℂ) :
    PowerSeries.coeff j (PowerSeries.monomial d c * f) =
      if d ≤ j then c * PowerSeries.coeff (j - d) f else 0 := by
  convert MvPowerSeries.coeff_monomial_mul
    (n := Finsupp.single () d) (m := Finsupp.single () j)
    (a := c) (f : MvPowerSeries Unit ℂ) using 1
  · by_cases h : d ≤ j
    · simp only [if_pos h]
      have hsub :
          (Finsupp.single () j - Finsupp.single () d : Unit →₀ ℕ) =
            Finsupp.single () (j - d) := by
        apply Finsupp.ext
        intro x
        cases x
        simp
      have hle :
          (Finsupp.single () d : Unit →₀ ℕ) ≤
            Finsupp.single () j := by
        intro x
        cases x
        simpa using h
      rw [if_pos hle, hsub]
      rfl
    · simp [h]

noncomputable def harcosPrimeEulerDenominator
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (q : HarcosPrimeUpTo p N) : PowerSeries ℂ :=
  1 - PowerSeries.monomial q.1.1.natDegree
    (harcosEtaPolynomial p a b q.1.1)

theorem harcosPrimeEulerDenominator_mul_geometric
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (q : HarcosPrimeUpTo p N) :
    harcosPrimeEulerDenominator p N a b q *
      harcosPrimeGeometricSeries p N a b q = 1 := by
  let e := harcosEtaPolynomial p a b q.1.1
  let D := q.1.1.natDegree
  have hD : 0 < D := harcosPrimeUpTo_degree_pos p N q
  ext j
  rw [harcosPrimeEulerDenominator, sub_mul, one_mul,
    map_sub, coeff_monomial_mul_nat]
  rw [coeff_harcosPrimeGeometricSeries,
    coeff_harcosPrimeGeometricSeries, PowerSeries.coeff_one]
  change (if D ∣ j then e ^ (j / D) else 0) -
      (if D ≤ j then
        e * (if D ∣ j - D then e ^ ((j - D) / D) else 0)
      else 0) = if j = 0 then 1 else 0
  by_cases hj0 : j = 0
  · subst j
    simp [hD.ne']
  · rw [if_neg hj0]
    by_cases hDj : D ≤ j
    · rw [if_pos hDj]
      by_cases hdvd : D ∣ j
      · obtain ⟨k, rfl⟩ := hdvd
        cases k with
        | zero => simp at hj0
        | succ k =>
            rw [if_pos (dvd_mul_right D (k + 1))]
            have hsub : D * (k + 1) - D = D * k := by
              rw [Nat.mul_succ, Nat.add_sub_cancel]
            rw [if_pos (by rw [hsub]; exact dvd_mul_right D k)]
            have hsub' : (k + 1) * D - D = k * D := by
              rw [Nat.succ_mul, Nat.add_sub_cancel_right]
            rw [mul_comm D (k + 1), Nat.mul_div_left _ hD, hsub',
              Nat.mul_div_left _ hD, pow_succ]
            ring
      · rw [if_neg hdvd]
        have hnsub : ¬ D ∣ j - D := by
          intro hsub
          apply hdvd
          rw [← Nat.sub_add_cancel hDj]
          exact dvd_add hsub (dvd_refl D)
        rw [if_neg hnsub]
        ring
    · rw [if_neg hDj]
      have hndvd : ¬ D ∣ j := by
        intro h
        obtain ⟨k, rfl⟩ := h
        have hk : k = 0 := by
          by_contra hk0
          have : D ≤ D * k := by
            exact Nat.le_mul_of_pos_right D (Nat.pos_of_ne_zero hk0)
          exact hDj this
        subst k
        simp at hj0
      rw [if_neg hndvd]
      ring

end

end RiemannZeta.GuthMaynard

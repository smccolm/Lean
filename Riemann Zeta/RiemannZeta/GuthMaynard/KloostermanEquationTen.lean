import RiemannZeta.GuthMaynard.KloostermanLocalEuler
import Mathlib.RingTheory.PowerSeries.Derivative

open Polynomial Classical
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

noncomputable section

/-- The `harcosPrimeUpToOfFactorAt` definition used by the source-facing construction in `KloostermanEquationTen`. -/
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

/-- The `HarcosEulerAllocationAt` definition used by the source-facing construction in `KloostermanEquationTen`. -/
def HarcosEulerAllocationAt
    (p N d : ℕ) [Fact p.Prime] :=
  {l : HarcosPrimeUpTo p N →₀ ℕ //
    l ∈ Finset.finsuppAntidiag Finset.univ d ∧
      ∀ q, q.1.1.natDegree ∣ l q}

/-- The `harcosEulerAllocationAtOfFactorization` definition used by the source-facing construction in `KloostermanEquationTen`. -/
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

/-- The `harcosFactorizationOfEulerAllocationAt` definition used by the source-facing construction in `KloostermanEquationTen`. -/
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

/-- The `harcosEulerAllocationAtEquiv` definition used by the source-facing construction in `KloostermanEquationTen`. -/
def harcosEulerAllocationAtEquiv
    (p N d : ℕ) [Fact p.Prime] (hdN : d ≤ N) :
    HarcosFactorization p d ≃ HarcosEulerAllocationAt p N d where
  toFun := harcosEulerAllocationAtOfFactorization p N d hdN
  invFun := harcosFactorizationOfEulerAllocationAt p N d
  left_inv := harcosEulerAllocationAt_factorization_left p N d hdN
  right_inv := harcosEulerAllocationAt_factorization_right p N d hdN

/-- The `harcosEulerAllocationAtWeight` definition used by the source-facing construction in `KloostermanEquationTen`. -/
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

/-- The `harcosEulerAllocationAtFinset` definition used by the source-facing construction in `KloostermanEquationTen`. -/
def harcosEulerAllocationAtFinset
    (p N d : ℕ) [Fact p.Prime] :
    Finset (HarcosPrimeUpTo p N →₀ ℕ) :=
  (Finset.finsuppAntidiag
    (Finset.univ : Finset (HarcosPrimeUpTo p N)) d).filter
      (fun l ↦ ∀ q, q.1.1.natDegree ∣ l q)

/-- The `harcosEulerAllocationAtSubtypeEquiv` definition used by the source-facing construction in `KloostermanEquationTen`. -/
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

/-- The `harcosPrimeEulerDenominator` definition used by the source-facing construction in `KloostermanEquationTen`. -/
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

theorem derivative_harcosPrimeEulerDenominator
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (q : HarcosPrimeUpTo p N) :
    PowerSeries.derivative ℂ (harcosPrimeEulerDenominator p N a b q) =
      -PowerSeries.monomial (q.1.1.natDegree - 1)
        ((q.1.1.natDegree : ℂ) *
          harcosEtaPolynomial p a b q.1.1) := by
  let D := q.1.1.natDegree
  let e := harcosEtaPolynomial p a b q.1.1
  have hD : 0 < D := harcosPrimeUpTo_degree_pos p N q
  ext j
  rw [PowerSeries.coeff_derivative]
  unfold harcosPrimeEulerDenominator
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_monomial,
    map_neg, PowerSeries.coeff_monomial]
  change ((if j + 1 = 0 then 1 else 0) -
      if j + 1 = D then e else 0) * (j + 1) =
    -(if j = D - 1 then (D : ℂ) * e else 0)
  by_cases h : j + 1 = D
  · have hj : j = D - 1 := by omega
    rw [if_pos h, if_pos hj, if_neg (Nat.succ_ne_zero j)]
    norm_num
    have hc : (j : ℂ) + 1 = (D : ℂ) := by exact_mod_cast h
    rw [hc]
    ring
  · have hj : j ≠ D - 1 := by
      intro hj
      apply h
      omega
    rw [if_neg h, if_neg hj, if_neg (Nat.succ_ne_zero j)]
    ring

/-- The `harcosPrimeLogDerivativeTerm` definition used by the source-facing construction in `KloostermanEquationTen`. -/
noncomputable def harcosPrimeLogDerivativeTerm
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (q : HarcosPrimeUpTo p N) : PowerSeries ℂ :=
  PowerSeries.monomial q.1.1.natDegree
      ((q.1.1.natDegree : ℂ) *
        harcosEtaPolynomial p a b q.1.1) *
    harcosPrimeGeometricSeries p N a b q

theorem harcosPrime_logDerivative_identity
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (q : HarcosPrimeUpTo p N) :
    PowerSeries.X * PowerSeries.derivative ℂ
        (harcosPrimeGeometricSeries p N a b q) =
      harcosPrimeGeometricSeries p N a b q *
        harcosPrimeLogDerivativeTerm p N a b q := by
  let D := harcosPrimeEulerDenominator p N a b q
  let G := harcosPrimeGeometricSeries p N a b q
  let d := q.1.1.natDegree
  let e := harcosEtaPolynomial p a b q.1.1
  let M := PowerSeries.monomial (d - 1) ((d : ℂ) * e)
  have hd : 0 < d := harcosPrimeUpTo_degree_pos p N q
  have hDG : D * G = 1 :=
    harcosPrimeEulerDenominator_mul_geometric p N a b q
  have hder := congrArg (PowerSeries.derivative ℂ) hDG
  rw [(PowerSeries.derivative ℂ).leibniz,
    (PowerSeries.derivative ℂ).map_one_eq_zero] at hder
  have hder' : D * PowerSeries.derivative ℂ G +
      G * PowerSeries.derivative ℂ D = 0 := by
    simpa [Algebra.smul_def] using hder
  have hsolve : PowerSeries.derivative ℂ G =
      -(G ^ 2 * PowerSeries.derivative ℂ D) := by
    have hpart : D * PowerSeries.derivative ℂ G =
        -(G * PowerSeries.derivative ℂ D) := by
      linear_combination hder'
    calc
      PowerSeries.derivative ℂ G =
          1 * PowerSeries.derivative ℂ G := by ring
      _ = (D * G) * PowerSeries.derivative ℂ G := by rw [hDG]
      _ = G * (D * PowerSeries.derivative ℂ G) := by ring
      _ = G * (-(G * PowerSeries.derivative ℂ D)) := by rw [hpart]
      _ = -(G ^ 2 * PowerSeries.derivative ℂ D) := by ring
  have hDder : PowerSeries.derivative ℂ D = -M := by
    exact derivative_harcosPrimeEulerDenominator p N a b q
  have hGder : PowerSeries.derivative ℂ G = G ^ 2 * M := by
    rw [hsolve, hDder]
    ring
  have hXM : PowerSeries.X * M =
      PowerSeries.monomial d ((d : ℂ) * e) := by
    change PowerSeries.X *
        PowerSeries.monomial (d - 1) ((d : ℂ) * e) = _
    rw [show (PowerSeries.X : PowerSeries ℂ) =
      PowerSeries.monomial 1 1 by
        simpa using (PowerSeries.X_pow_eq (R := ℂ) 1)]
    rw [PowerSeries.monomial_mul_monomial]
    rw [one_mul, show 1 + (d - 1) = d by omega]
  rw [hGder]
  change PowerSeries.X * (G ^ 2 * M) =
    G * (PowerSeries.monomial d ((d : ℂ) * e) * G)
  rw [← hXM]
  ring

theorem X_derivative_finsetProd
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (G B : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s,
      PowerSeries.X * PowerSeries.derivative ℂ (G i) = G i * B i) :
    PowerSeries.X * PowerSeries.derivative ℂ (∏ i ∈ s, G i) =
      (∏ i ∈ s, G i) * (∑ i ∈ s, B i) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [(PowerSeries.derivative ℂ).map_one_eq_zero]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        (PowerSeries.derivative ℂ).leibniz]
      simp only [Algebra.smul_def, Algebra.algebraMap_self,
        RingHom.id_apply]
      calc
        PowerSeries.X *
            (G i * PowerSeries.derivative ℂ (∏ x ∈ s, G x) +
              (∏ x ∈ s, G x) * PowerSeries.derivative ℂ (G i)) =
            G i * (PowerSeries.X *
              PowerSeries.derivative ℂ (∏ x ∈ s, G x)) +
              (∏ x ∈ s, G x) *
                (PowerSeries.X * PowerSeries.derivative ℂ (G i)) := by ring
        _ = G i * ((∏ x ∈ s, G x) * (∑ x ∈ s, B x)) +
              (∏ x ∈ s, G x) * (G i * B i) := by
          rw [ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)),
            h i (Finset.mem_insert_self i s)]
        _ = (G i * ∏ x ∈ s, G x) * (B i + ∑ x ∈ s, B x) := by
          ring

/-- The `harcosFinitePrimeLogDerivative` definition used by the source-facing construction in `KloostermanEquationTen`. -/
noncomputable def harcosFinitePrimeLogDerivative
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) : PowerSeries ℂ :=
  ∑ q : HarcosPrimeUpTo p N,
    harcosPrimeLogDerivativeTerm p N a b q

theorem harcosFiniteEulerProduct_logDerivative
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    PowerSeries.X * PowerSeries.derivative ℂ
        (harcosFiniteEulerProduct p N a b) =
      harcosFiniteEulerProduct p N a b *
        harcosFinitePrimeLogDerivative p N a b := by
  unfold harcosFiniteEulerProduct harcosFinitePrimeLogDerivative
  rw [show (∏ q : HarcosPrimeUpTo p N,
      harcosPrimeGeometricSeries p N a b q) =
      ∏ q ∈ (Finset.univ : Finset (HarcosPrimeUpTo p N)),
        harcosPrimeGeometricSeries p N a b q by simp]
  rw [show (∑ q : HarcosPrimeUpTo p N,
      harcosPrimeLogDerivativeTerm p N a b q) =
      ∑ q ∈ (Finset.univ : Finset (HarcosPrimeUpTo p N)),
        harcosPrimeLogDerivativeTerm p N a b q by simp]
  apply X_derivative_finsetProd
  intro q _hq
  exact harcosPrime_logDerivative_identity p N a b q

/-- The `harcosPrimePowerSum` definition used by the source-facing construction in `KloostermanEquationTen`. -/
noncomputable def harcosPrimePowerSum
    (p N n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) : ℂ :=
  ∑ q : HarcosPrimeUpTo p N,
    if q.1.1.natDegree ∣ n then
      (q.1.1.natDegree : ℂ) *
        harcosEtaPolynomial p a b q.1.1 ^
          (n / q.1.1.natDegree)
    else 0

theorem coeff_harcosPrimeLogDerivativeTerm
    (p N n : ℕ) [NeZero p] [Fact p.Prime]
    (hn : 0 < n) (a b : ZMod p) (q : HarcosPrimeUpTo p N) :
    PowerSeries.coeff n (harcosPrimeLogDerivativeTerm p N a b q) =
      if q.1.1.natDegree ∣ n then
        (q.1.1.natDegree : ℂ) *
          harcosEtaPolynomial p a b q.1.1 ^
            (n / q.1.1.natDegree)
      else 0 := by
  let d := q.1.1.natDegree
  let e := harcosEtaPolynomial p a b q.1.1
  have hd : 0 < d := harcosPrimeUpTo_degree_pos p N q
  unfold harcosPrimeLogDerivativeTerm
  rw [coeff_monomial_mul_nat]
  by_cases hdvd : d ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    have hk : 0 < k := by
      by_contra hk0
      simp only [Nat.not_lt, Nat.le_zero] at hk0
      subst k
      simp at hn
    cases k with
    | zero => simp at hk
    | succ k =>
        rw [if_pos (dvd_mul_right d (k + 1))]
        have hle : d ≤ d * (k + 1) := by
          exact Nat.le_mul_of_pos_right d (by omega)
        rw [if_pos hle, coeff_harcosPrimeGeometricSeries]
        have hsub : d * (k + 1) - d = d * k := by
          rw [Nat.mul_succ, Nat.add_sub_cancel]
        rw [if_pos (by rw [hsub]; exact dvd_mul_right d k)]
        change (d : ℂ) * e * e ^ ((d * (k + 1) - d) / d) =
          (d : ℂ) * e ^ (d * (k + 1) / d)
        rw [hsub, mul_comm d k, Nat.mul_div_left _ hd,
          mul_comm d (k + 1), Nat.mul_div_left _ hd, pow_succ]
        ring
  · rw [if_neg hdvd]
    by_cases hle : d ≤ n
    · rw [if_pos hle, coeff_harcosPrimeGeometricSeries]
      have hnsub : ¬ d ∣ n - d := by
        intro hsub
        apply hdvd
        rw [← Nat.sub_add_cancel hle]
        exact dvd_add hsub (dvd_refl d)
      rw [if_neg hnsub]
      ring
    · rw [if_neg hle]

theorem coeff_harcosFinitePrimeLogDerivative
    (p N n : ℕ) [NeZero p] [Fact p.Prime]
    (hn : 0 < n) (a b : ZMod p) :
    PowerSeries.coeff n (harcosFinitePrimeLogDerivative p N a b) =
      harcosPrimePowerSum p N n a b := by
  unfold harcosFinitePrimeLogDerivative harcosPrimePowerSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  exact coeff_harcosPrimeLogDerivativeTerm p N n hn a b q

theorem coeff_X_mul_derivative
    (n : ℕ) (hn : 0 < n) (f : PowerSeries ℂ) :
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative ℂ f) =
      (n : ℂ) * PowerSeries.coeff n f := by
  rw [show (PowerSeries.X : PowerSeries ℂ) =
    PowerSeries.monomial 1 1 by
      simpa using (PowerSeries.X_pow_eq (R := ℂ) 1)]
  rw [coeff_monomial_mul_nat, if_pos (by omega),
    PowerSeries.coeff_derivative]
  have hidx : n - 1 + 1 = n := by omega
  rw [hidx]
  have hcast : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
    exact_mod_cast (show n - 1 + 1 = n by omega)
  rw [← hcast]
  ring

theorem harcosEquationNine_logDerivative_truncated
    (p N n : ℕ) [NeZero p] [Fact p.Prime]
    (hn : 0 < n) (hnN : n ≤ N) (a b : ZMod p) :
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative ℂ (harcosLSeries p a b)) =
      PowerSeries.coeff n
        (harcosLSeries p a b *
          harcosFinitePrimeLogDerivative p N a b) := by
  let P := harcosFiniteEulerProduct p N a b
  let B := harcosFinitePrimeLogDerivative p N a b
  have hlog := harcosFiniteEulerProduct_logDerivative p N a b
  calc
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative ℂ (harcosLSeries p a b)) =
        (n : ℂ) * PowerSeries.coeff n (harcosLSeries p a b) :=
      coeff_X_mul_derivative n hn _
    _ = (n : ℂ) * PowerSeries.coeff n P := by
      rw [harcosEquationNine_truncated p N n hnN]
    _ = PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative ℂ P) :=
      (coeff_X_mul_derivative n hn P).symm
    _ = PowerSeries.coeff n (P * B) := congrArg (PowerSeries.coeff n) hlog
    _ = PowerSeries.coeff n (harcosLSeries p a b * B) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
      have hiN : ij.1 ≤ N := by omega
      rw [harcosEquationNine_truncated p N ij.1 hiN]

theorem harcosLSeries_eq_explicit
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosLSeries p a b =
      1 + PowerSeries.C (kloostermanSumZMod p a b) * PowerSeries.X +
        PowerSeries.C (p : ℂ) * PowerSeries.X ^ 2 := by
  ext d
  simp only [harcosLSeries, PowerSeries.coeff_mk, map_add,
    PowerSeries.coeff_one, PowerSeries.coeff_C_mul_X_pow]
  rw [harcosEtaDegreeSum_eq p d a b ha hb]
  by_cases h0 : d = 0
  · subst d
    simp
  by_cases h1 : d = 1
  · subst d
    simp
  by_cases h2 : d = 2
  · subst d
    simp
  rw [if_neg h0, if_neg h1, if_neg h2]
  simp [PowerSeries.coeff_X, h0, h1]

theorem coeff_explicitL_mul
    (p n : ℕ) [NeZero p]
    (a b : ZMod p) (B : PowerSeries ℂ) :
    PowerSeries.coeff n
      ((1 + PowerSeries.C (kloostermanSumZMod p a b) * PowerSeries.X +
          PowerSeries.C (p : ℂ) * PowerSeries.X ^ 2) * B) =
      PowerSeries.coeff n B +
        (if 1 ≤ n then kloostermanSumZMod p a b *
          PowerSeries.coeff (n - 1) B else 0) +
        (if 2 ≤ n then (p : ℂ) *
          PowerSeries.coeff (n - 2) B else 0) := by
  rw [add_mul, add_mul, one_mul, map_add, map_add]
  have h1 : PowerSeries.C (kloostermanSumZMod p a b) * PowerSeries.X =
      PowerSeries.monomial 1 (kloostermanSumZMod p a b) := by
    ext j
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
      PowerSeries.coeff_monomial]
    split <;> simp_all
  have h2 : PowerSeries.C (p : ℂ) * PowerSeries.X ^ 2 =
      PowerSeries.monomial 2 (p : ℂ) := by
    ext j
    rw [PowerSeries.coeff_C_mul_X_pow,
      PowerSeries.coeff_monomial]
  rw [h1, h2, coeff_monomial_mul_nat, coeff_monomial_mul_nat]

theorem coeff_X_derivative_explicitL
    (p n : ℕ) [NeZero p]
    (a b : ZMod p) :
    PowerSeries.coeff n
      (PowerSeries.X * PowerSeries.derivative ℂ
        (1 + PowerSeries.C (kloostermanSumZMod p a b) * PowerSeries.X +
          PowerSeries.C (p : ℂ) * PowerSeries.X ^ 2)) =
      if n = 1 then kloostermanSumZMod p a b
      else if n = 2 then 2 * (p : ℂ)
      else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [PowerSeries.coeff_zero_X_mul]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  rw [coeff_X_mul_derivative n hn]
  simp only [map_add, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul_X_pow]
  by_cases h1 : n = 1
  · subst n
    simp
  by_cases h2 : n = 2
  · subst n
    norm_num
  rw [if_neg h1, if_neg h2]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X, if_neg h1]
  simp [hn0, h2]

theorem constantCoeff_harcosFinitePrimeLogDerivative
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    PowerSeries.constantCoeff
        (harcosFinitePrimeLogDerivative p N a b) = 0 := by
  unfold harcosFinitePrimeLogDerivative
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro q _hq
  unfold harcosPrimeLogDerivativeTerm
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_monomial_mul_nat]
  have hd := harcosPrimeUpTo_degree_pos p N q
  rw [if_neg (by omega)]

theorem harcosPrimePowerSum_one
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (hN : 1 ≤ N) :
    harcosPrimePowerSum p N 1 a b = kloostermanSumZMod p a b := by
  have hlog := harcosEquationNine_logDerivative_truncated
    p N 1 (by omega) hN a b
  rw [harcosLSeries_eq_explicit p a b ha hb,
    coeff_X_derivative_explicitL,
    coeff_explicitL_mul,
    coeff_harcosFinitePrimeLogDerivative p N 1 (by omega)] at hlog
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_harcosFinitePrimeLogDerivative] at hlog
  simpa using hlog.symm

theorem harcosPrimePowerSum_two
    (p N : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (hN : 2 ≤ N) :
    harcosPrimePowerSum p N 2 a b =
      2 * (p : ℂ) - kloostermanSumZMod p a b ^ 2 := by
  have hlog := harcosEquationNine_logDerivative_truncated
    p N 2 (by omega) hN a b
  rw [harcosLSeries_eq_explicit p a b ha hb,
    coeff_X_derivative_explicitL,
    coeff_explicitL_mul,
    coeff_harcosFinitePrimeLogDerivative p N 2 (by omega),
    coeff_harcosFinitePrimeLogDerivative p N 1 (by omega)] at hlog
  have hB1 := harcosPrimePowerSum_one p N a b ha hb (by omega)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_harcosFinitePrimeLogDerivative] at hlog
  rw [hB1] at hlog
  norm_num at hlog
  calc
    harcosPrimePowerSum p N 2 a b =
        2 * (p : ℂ) - kloostermanSumZMod p a b *
          kloostermanSumZMod p a b := by
      apply (eq_sub_iff_add_eq).2
      exact hlog.symm
    _ = 2 * (p : ℂ) - kloostermanSumZMod p a b ^ 2 := by ring

theorem harcosPrimePowerSum_recurrence
    (p N n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (hn : 3 ≤ n) (hnN : n ≤ N) :
    harcosPrimePowerSum p N n a b =
      -kloostermanSumZMod p a b *
          harcosPrimePowerSum p N (n - 1) a b -
        (p : ℂ) * harcosPrimePowerSum p N (n - 2) a b := by
  have hlog := harcosEquationNine_logDerivative_truncated
    p N n (by omega) hnN a b
  rw [harcosLSeries_eq_explicit p a b ha hb,
    coeff_X_derivative_explicitL,
    coeff_explicitL_mul] at hlog
  rw [coeff_harcosFinitePrimeLogDerivative p N n (by omega),
    coeff_harcosFinitePrimeLogDerivative p N (n - 1) (by omega),
    coeff_harcosFinitePrimeLogDerivative p N (n - 2) (by omega)] at hlog
  simp only [show n ≠ 1 by omega, show n ≠ 2 by omega,
    if_false, show 1 ≤ n by omega, show 2 ≤ n by omega,
    if_true] at hlog
  calc
    harcosPrimePowerSum p N n a b =
        -(kloostermanSumZMod p a b *
          harcosPrimePowerSum p N (n - 1) a b +
          (p : ℂ) * harcosPrimePowerSum p N (n - 2) a b) := by
      linear_combination -hlog
    _ = -kloostermanSumZMod p a b *
          harcosPrimePowerSum p N (n - 1) a b -
        (p : ℂ) * harcosPrimePowerSum p N (n - 2) a b := by ring

/-- The `harcosNegativeRootPower` definition used by the source-facing construction in `KloostermanEquationTen`. -/
noncomputable def harcosNegativeRootPower
    (p n : ℕ) [NeZero p] (a b : ZMod p) : ℂ :=
  -(kloostermanAlpha p a b ^ n + kloostermanBeta p a b ^ n)

theorem harcosNegativeRootPower_one
    (p : ℕ) [NeZero p] (a b : ZMod p) :
    harcosNegativeRootPower p 1 a b = kloostermanSumZMod p a b := by
  unfold harcosNegativeRootPower
  rw [pow_one, pow_one, kloostermanAlpha_add_beta]
  ring

theorem harcosNegativeRootPower_two
    (p : ℕ) [NeZero p] (a b : ZMod p) :
    harcosNegativeRootPower p 2 a b =
      2 * (p : ℂ) - kloostermanSumZMod p a b ^ 2 := by
  unfold harcosNegativeRootPower
  have hadd := kloostermanAlpha_add_beta p a b
  have hmul := kloostermanAlpha_mul_beta p a b
  calc
    -(kloostermanAlpha p a b ^ 2 + kloostermanBeta p a b ^ 2) =
        2 * (kloostermanAlpha p a b * kloostermanBeta p a b) -
          (kloostermanAlpha p a b + kloostermanBeta p a b) ^ 2 := by ring
    _ = 2 * (p : ℂ) - (-kloostermanSumZMod p a b) ^ 2 := by
      rw [hmul, hadd]
    _ = 2 * (p : ℂ) - kloostermanSumZMod p a b ^ 2 := by ring

theorem harcosNegativeRootPower_recurrence
    (p n : ℕ) [NeZero p] (a b : ZMod p) (hn : 2 ≤ n) :
    harcosNegativeRootPower p n a b =
      -kloostermanSumZMod p a b *
          harcosNegativeRootPower p (n - 1) a b -
        (p : ℂ) * harcosNegativeRootPower p (n - 2) a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  unfold harcosNegativeRootPower
  have hadd := kloostermanAlpha_add_beta p a b
  have hmul := kloostermanAlpha_mul_beta p a b
  have htop : 2 + k = k + 2 := by omega
  have hprev : k + 2 - 1 = k + 1 := by omega
  have hprev2 : k + 2 - 2 = k := by omega
  rw [htop, hprev, hprev2]
  calc
    -(kloostermanAlpha p a b ^ (k + 2) +
        kloostermanBeta p a b ^ (k + 2)) =
        (kloostermanAlpha p a b + kloostermanBeta p a b) *
            (-(kloostermanAlpha p a b ^ (k + 1) +
              kloostermanBeta p a b ^ (k + 1))) -
          (kloostermanAlpha p a b * kloostermanBeta p a b) *
            (-(kloostermanAlpha p a b ^ k +
              kloostermanBeta p a b ^ k)) := by
      rw [show k + 2 = (k + 1) + 1 by omega,
        show k + 1 = k + 1 by rfl]
      simp only [pow_succ]
      ring
    _ = -kloostermanSumZMod p a b *
          (-(kloostermanAlpha p a b ^ (k + 1) +
            kloostermanBeta p a b ^ (k + 1))) -
        (p : ℂ) * (-(kloostermanAlpha p a b ^ k +
          kloostermanBeta p a b ^ k)) := by rw [hadd, hmul]

theorem harcosPrimePowerSum_eq_negativeRootPower
    (p N n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (hn : 0 < n) (hnN : n ≤ N) :
    harcosPrimePowerSum p N n a b =
      harcosNegativeRootPower p n a b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · omega
      · exact (harcosPrimePowerSum_one p N a b ha hb (by omega)).trans
          (harcosNegativeRootPower_one p a b).symm
      · rcases n with _ | n
        · exact (harcosPrimePowerSum_two p N a b ha hb (by omega)).trans
            (harcosNegativeRootPower_two p a b).symm
        · have hn3 : 3 ≤ n + 3 := by omega
          rw [harcosPrimePowerSum_recurrence p N (n + 3) a b ha hb hn3 hnN]
          have hsub1 : n + 3 - 1 = n + 2 := by omega
          have hsub2 : n + 3 - 2 = n + 1 := by omega
          rw [hsub1, hsub2]
          rw [ih (n + 2) (by omega) (by omega) (by omega),
            ih (n + 1) (by omega) (by omega) (by omega)]
          have hr := harcosNegativeRootPower_recurrence p (n + 3) a b
            (by omega)
          rw [hsub1, hsub2] at hr
          simpa [show n + 3 = n + 1 + 1 + 1 by omega] using hr.symm

/-- The `HarcosIrreducibleMonicDegree` definition used by the source-facing construction in `KloostermanEquationTen`. -/
def HarcosIrreducibleMonicDegree
    (p d : ℕ) [Fact p.Prime] :=
  {q : HarcosIrreducibleMonic p // q.1.natDegree = d}

/-- The `harcosIrreducibleMonicDegreeEquiv` definition used by the source-facing construction in `KloostermanEquationTen`. -/
def harcosIrreducibleMonicDegreeEquiv
    (p d : ℕ) [Fact p.Prime] :
    HarcosIrreducibleMonicDegree p d ≃
      {q : HarcosPrimeUpTo p d // q.1.1.natDegree = d} where
  toFun q := ⟨⟨q.1, q.2.le⟩, q.2⟩
  invFun q := ⟨q.1.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance harcosIrreducibleMonicDegreeFintype
    (p d : ℕ) [Fact p.Prime] :
    Fintype (HarcosIrreducibleMonicDegree p d) :=
  Fintype.ofEquiv {q : HarcosPrimeUpTo p d // q.1.1.natDegree = d}
    (harcosIrreducibleMonicDegreeEquiv p d).symm

/-- The `HarcosEquationTenIndex` definition used by the source-facing construction in `KloostermanEquationTen`. -/
def HarcosEquationTenIndex
    (p n : ℕ) [Fact p.Prime] :=
  Σ d : {d // d ∈ n.divisors}, HarcosIrreducibleMonicDegree p d.1

/-- The `HarcosPrimeDividingDegree` definition used by the source-facing construction in `KloostermanEquationTen`. -/
def HarcosPrimeDividingDegree
    (p n : ℕ) [Fact p.Prime] :=
  {q : HarcosPrimeUpTo p n // q.1.1.natDegree ∣ n}

noncomputable instance harcosEquationTenIndexFintype
    (p n : ℕ) [Fact p.Prime] : Fintype (HarcosEquationTenIndex p n) := by
  unfold HarcosEquationTenIndex
  infer_instance

noncomputable instance harcosPrimeDividingDegreeFintype
    (p n : ℕ) [Fact p.Prime] :
    Fintype (HarcosPrimeDividingDegree p n) := by
  unfold HarcosPrimeDividingDegree
  infer_instance

/-- The `harcosEquationTenIndexEquiv` definition used by the source-facing construction in `KloostermanEquationTen`. -/
def harcosEquationTenIndexEquiv
    (p n : ℕ) [Fact p.Prime] (hn : 0 < n) :
    HarcosEquationTenIndex p n ≃ HarcosPrimeDividingDegree p n where
  toFun z := by
    let d := z.1.1
    have hdvd : d ∣ n := Nat.mem_divisors.mp z.1.2 |>.1
    have hdn : d ≤ n := Nat.le_of_dvd hn hdvd
    exact ⟨⟨z.2.1, z.2.2.le.trans hdn⟩, by simpa [z.2.2] using hdvd⟩
  invFun q := by
    let d := q.1.1.1.natDegree
    have hdvd : d ∣ n := q.2
    have hdpos : 0 < d := harcosPrimeUpTo_degree_pos p n q.1
    exact ⟨⟨d, Nat.mem_divisors.mpr ⟨hdvd, hn.ne'⟩⟩,
      ⟨q.1.1, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨⟨d, hd⟩, ⟨q, hq⟩⟩
    dsimp
    change q.1.natDegree = d at hq
    subst d
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The `harcosEquationTenDivisorSum` definition used by the source-facing construction in `KloostermanEquationTen`. -/
noncomputable def harcosEquationTenDivisorSum
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) : ℂ :=
  ∑ d ∈ n.divisors,
    ∑ q : HarcosIrreducibleMonicDegree p d,
      (d : ℂ) * harcosEtaPolynomial p a b q.1.1 ^ (n / d)

theorem harcosEquationTenDivisorSum_eq_sigma
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    harcosEquationTenDivisorSum p n a b =
      ∑ z : HarcosEquationTenIndex p n,
        (z.1.1 : ℂ) * harcosEtaPolynomial p a b z.2.1.1 ^
          (n / z.1.1) := by
  unfold harcosEquationTenDivisorSum HarcosEquationTenIndex
  calc
    (∑ d ∈ n.divisors,
        ∑ q : HarcosIrreducibleMonicDegree p d,
          (d : ℂ) * harcosEtaPolynomial p a b q.1.1 ^ (n / d)) =
        ∑ d : {d // d ∈ n.divisors},
          ∑ q : HarcosIrreducibleMonicDegree p d.1,
            (d.1 : ℂ) * harcosEtaPolynomial p a b q.1.1 ^
              (n / d.1) := by
      apply Finset.sum_subtype
      intro d
      rfl
    _ = ∑ z : Σ d : {d // d ∈ n.divisors},
        HarcosIrreducibleMonicDegree p d.1,
          (z.1.1 : ℂ) * harcosEtaPolynomial p a b z.2.1.1 ^
            (n / z.1.1) := by
      symm
      exact Fintype.sum_sigma'
        (fun (d : {d // d ∈ n.divisors})
          (q : HarcosIrreducibleMonicDegree p d.1) ↦ (d.1 : ℂ) *
          harcosEtaPolynomial p a b q.1.1 ^ (n / d.1))

theorem harcosPrimePowerSum_eq_subtype
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    harcosPrimePowerSum p n n a b =
      ∑ q : HarcosPrimeDividingDegree p n,
        (q.1.1.1.natDegree : ℂ) *
          harcosEtaPolynomial p a b q.1.1.1 ^
            (n / q.1.1.1.natDegree) := by
  unfold harcosPrimePowerSum HarcosPrimeDividingDegree
  symm
  calc
    (∑ q : {q : HarcosPrimeUpTo p n // q.1.1.natDegree ∣ n},
        (q.1.1.1.natDegree : ℂ) *
          harcosEtaPolynomial p a b q.1.1.1 ^
            (n / q.1.1.1.natDegree)) =
        ∑ q ∈ (Finset.univ.filter
            (fun q : HarcosPrimeUpTo p n ↦ q.1.1.natDegree ∣ n)),
          (q.1.1.natDegree : ℂ) *
            harcosEtaPolynomial p a b q.1.1 ^
              (n / q.1.1.natDegree) := by
      symm
      apply Finset.sum_subtype
      intro q
      simp
    _ = ∑ q : HarcosPrimeUpTo p n,
        if q.1.1.natDegree ∣ n then
          (q.1.1.natDegree : ℂ) *
            harcosEtaPolynomial p a b q.1.1 ^
              (n / q.1.1.natDegree)
        else 0 := by
      simp only [Finset.sum_filter]

theorem harcosEquationTenDivisorSum_eq_primePowerSum
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (hn : 0 < n) :
    harcosEquationTenDivisorSum p n a b =
      harcosPrimePowerSum p n n a b := by
  rw [harcosEquationTenDivisorSum_eq_sigma,
    harcosPrimePowerSum_eq_subtype]
  apply Fintype.sum_equiv (harcosEquationTenIndexEquiv p n hn)
  intro z
  rcases z with ⟨⟨d, hd⟩, ⟨q, hq⟩⟩
  dsimp [harcosEquationTenIndexEquiv]
  change q.1.natDegree = d at hq
  subst d
  rfl

/-- Harcos equation (10), in its literal divisor/irreducible-polynomial form. -/
theorem harcosEquationTen
    (p n : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hn : 0 < n) :
    -(kloostermanAlpha p a b ^ n + kloostermanBeta p a b ^ n) =
      ∑ d ∈ n.divisors,
        ∑ q : HarcosIrreducibleMonicDegree p d,
          (d : ℂ) * harcosEtaPolynomial p a b q.1.1 ^ (n / d) := by
  change harcosNegativeRootPower p n a b =
    harcosEquationTenDivisorSum p n a b
  rw [harcosEquationTenDivisorSum_eq_primePowerSum p n a b hn]
  exact (harcosPrimePowerSum_eq_negativeRootPower
    p n n a b ha hb hn le_rfl).symm

end

end RiemannZeta.GuthMaynard

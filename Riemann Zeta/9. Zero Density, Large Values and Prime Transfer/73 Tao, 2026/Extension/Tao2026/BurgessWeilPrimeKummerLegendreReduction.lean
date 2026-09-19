import Tao2026.BurgessWeilPrimeKummerTwoPointNormalization

/-!
# Legendre reduction of the three-root Kummer source

After two-point normalization, an exactly-three-root monic split polynomial
is determined by a third root `t ≠ 0,1` and the positive multiplicities at
`0`, `1`, and `t`.  This file constructs that polynomial canonically from
its root multiset and proves the representation literally.

The degree-divisible three-root case already has an explicit Jacobi-sum
Frobenius system.  Consequently the remaining source splits exactly into
the nondivisible finite-exponent Legendre family and the normalized family
with at least four distinct roots.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def primeKummerLegendrePolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p) : Polynomial (ZMod p) :=
  ((Multiset.replicate m 0 + Multiset.replicate n 1 +
      Multiset.replicate k t).map fun r => X - C r).prod

theorem primeKummerLegendrePolynomial_monic
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p) : (primeKummerLegendrePolynomial m n k t).Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C _

theorem primeKummerLegendrePolynomial_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p) :
    (primeKummerLegendrePolynomial m n k t).roots =
      Multiset.replicate m 0 + Multiset.replicate n 1 +
        Multiset.replicate k t := by
  exact Polynomial.roots_multiset_prod_X_sub_C _

theorem primeKummerLegendrePolynomial_splits
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p) : (primeKummerLegendrePolynomial m n k t).Splits := by
  apply Polynomial.Splits.multisetProd
  intro f hf
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hf
  exact Polynomial.Splits.X_sub_C r

theorem primeKummerLegendrePolynomial_natDegree
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p) :
    (primeKummerLegendrePolynomial m n k t).natDegree = m + n + k := by
  rw [(primeKummerLegendrePolynomial_splits m n k t).natDegree_eq_card_roots,
    primeKummerLegendrePolynomial_roots]
  simp [add_assoc]

theorem primeKummerLegendrePolynomial_roots_toFinset
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) :
    (primeKummerLegendrePolynomial m n k t).roots.toFinset = {0, 1, t} := by
  rw [primeKummerLegendrePolynomial_roots]
  ext x
  simp [hm.ne', hn.ne', hk.ne']

theorem primeKummerLegendrePolynomial_rootMultiplicity_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p) (ht0 : t ≠ 0) :
    (primeKummerLegendrePolynomial m n k t).rootMultiplicity 0 = m := by
  rw [← Polynomial.count_roots, primeKummerLegendrePolynomial_roots]
  rw [Multiset.count_add, Multiset.count_add,
    Multiset.count_replicate_self, Multiset.count_replicate,
    Multiset.count_replicate]
  simp [ht0]

theorem primeKummerLegendrePolynomial_rootMultiplicity_one
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p) (ht1 : t ≠ 1) :
    (primeKummerLegendrePolynomial m n k t).rootMultiplicity 1 = n := by
  rw [← Polynomial.count_roots, primeKummerLegendrePolynomial_roots]
  rw [Multiset.count_add, Multiset.count_add,
    Multiset.count_replicate, Multiset.count_replicate_self,
    Multiset.count_replicate]
  simp [ht1]

theorem primeKummerLegendrePolynomial_rootMultiplicity_t
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (m n k : ℕ) (t : ZMod p) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (primeKummerLegendrePolynomial m n k t).rootMultiplicity t = k := by
  rw [← Polynomial.count_roots, primeKummerLegendrePolynomial_roots]
  rw [Multiset.count_add, Multiset.count_add,
    Multiset.count_replicate, Multiset.count_replicate,
    Multiset.count_replicate_self]
  simp [Ne.symm ht0, Ne.symm ht1]

theorem primeKummerLegendrePolynomial_reduced
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (hmred : m < orderOf χ) (hnred : n < orderOf χ)
    (hkred : k < orderOf χ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    IsPrimeKummerReducedExponentPolynomial χ (primeKummerLegendrePolynomial m n k t) := by
  intro a ha
  rw [primeKummerLegendrePolynomial_roots_toFinset m n k t hm hn hk] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha | ha
  · subst a
    rwa [primeKummerLegendrePolynomial_rootMultiplicity_zero m n k t ht0]
  · subst a
    rwa [primeKummerLegendrePolynomial_rootMultiplicity_one m n k t ht1]
  · subst a
    rwa [primeKummerLegendrePolynomial_rootMultiplicity_t m n k t ht0 ht1]

theorem exists_third_primeKummer_root
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p))
    (hzero : 0 ∈ P.roots.toFinset) (hone : 1 ∈ P.roots.toFinset)
    (hcard : P.roots.toFinset.card = 3) :
    ∃ t : ZMod p, t ≠ 0 ∧ t ≠ 1 ∧ P.roots.toFinset = {0, 1, t} := by
  let S := (P.roots.toFinset.erase 0).erase 1
  have hzeroOne : (0 : ZMod p) ≠ 1 := zero_ne_one
  have honeErase : 1 ∈ P.roots.toFinset.erase 0 :=
    Finset.mem_erase.mpr ⟨hzeroOne.symm, hone⟩
  have hcardErase0 : (P.roots.toFinset.erase 0).card = 2 := by
    rw [Finset.card_erase_of_mem hzero, hcard]
  have hScard : S.card = 1 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem honeErase, hcardErase0]
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hScard
  refine ⟨t, ?_, ?_, ?_⟩
  · intro ht0
    subst t
    have : 0 ∉ S := by simp [S]
    rw [ht] at this
    simp at this
  · intro ht1
    subst t
    have : 1 ∉ S := by simp [S]
    rw [ht] at this
    simp at this
  · ext x
    by_cases hx0 : x = 0
    · subst x
      simp [hzero]
    by_cases hx1 : x = 1
    · subst x
      simp [hone]
    have hmemS : x ∈ S ↔ x ∈ P.roots.toFinset := by
      simp [S, hx0, hx1]
    rw [← hmemS, ht]
    simp [hx0, hx1]

theorem eq_primeKummerLegendrePolynomial_of_threeRoots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (t : ZMod p)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hP : P.Splits) (hmonic : P.Monic)
    (hroots : P.roots.toFinset = {0, 1, t}) :
    P = primeKummerLegendrePolynomial (P.rootMultiplicity 0)
      (P.rootMultiplicity 1) (P.rootMultiplicity t) t := by
  let Q := primeKummerLegendrePolynomial (P.rootMultiplicity 0)
    (P.rootMultiplicity 1) (P.rootMultiplicity t) t
  have hrootsEq : P.roots = Q.roots := by
    rw [show Q.roots =
        Multiset.replicate (P.rootMultiplicity 0) 0 +
          Multiset.replicate (P.rootMultiplicity 1) 1 +
            Multiset.replicate (P.rootMultiplicity t) t by
      exact primeKummerLegendrePolynomial_roots _ _ _ _]
    ext x
    by_cases hx0 : x = 0
    · subst x
      rw [Multiset.count_add, Multiset.count_add,
        Multiset.count_replicate_self, Multiset.count_replicate,
        Multiset.count_replicate, Polynomial.count_roots]
      simp [ht0]
    by_cases hx1 : x = 1
    · subst x
      rw [Multiset.count_add, Multiset.count_add,
        Multiset.count_replicate, Multiset.count_replicate_self,
        Multiset.count_replicate, Polynomial.count_roots]
      simp [ht1]
    by_cases hxt : x = t
    · subst x
      rw [Multiset.count_add, Multiset.count_add,
        Multiset.count_replicate, Multiset.count_replicate,
        Multiset.count_replicate_self, Polynomial.count_roots]
      simp [Ne.symm ht0, Ne.symm ht1]
    · have hxnot : x ∉ P.roots := by
        intro hx
        have hx' := Multiset.mem_toFinset.mpr hx
        rw [hroots] at hx'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with rfl | rfl | rfl <;> contradiction
      rw [Multiset.count_eq_zero.mpr hxnot, Multiset.count_add,
        Multiset.count_add, Multiset.count_replicate,
        Multiset.count_replicate, Multiset.count_replicate]
      simp [Ne.symm hx0, Ne.symm hx1, Ne.symm hxt]
  have hQsplits : Q.Splits := by
    exact primeKummerLegendrePolynomial_splits _ _ _ _
  have hQmonic : Q.Monic := by
    exact primeKummerLegendrePolynomial_monic _ _ _ _
  calc
    P = (P.roots.map fun r => X - C r).prod :=
      hP.eq_prod_roots_of_monic hmonic
    _ = (Q.roots.map fun r => X - C r).prod := by rw [hrootsEq]
    _ = Q := (hQsplits.eq_prod_roots_of_monic hQmonic).symm

def TaoPrimeKummerLegendreReducedExponentFrobeniusSystem : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ
          (primeKummerLegendrePolynomial m n k t))

def TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Monic → P.Splits →
      IsPrimeKummerReducedExponentPolynomial χ P →
      0 ∈ P.roots.toFinset → 1 ∈ P.roots.toFinset →
      4 ≤ P.roots.toFinset.card →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

def TaoPrimeKummerLegendreOrFourRootsFrobeniusSystem : Prop := TaoPrimeKummerLegendreReducedExponentFrobeniusSystem ∧ TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemFourRootsOrMore

theorem taoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemThreeRootsOrMore_iff_legendreOrFourRoots :
    TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemThreeRootsOrMore ↔
      TaoPrimeKummerLegendreOrFourRootsFrobeniusSystem := by
  constructor
  · intro h
    constructor
    · intro p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 _hsum
      have hroots := primeKummerLegendrePolynomial_roots_toFinset m n k t hm hn hk
      apply h p χ (primeKummerLegendrePolynomial m n k t) hχ
        (primeKummerLegendrePolynomial_monic m n k t) (primeKummerLegendrePolynomial_splits m n k t)
        (primeKummerLegendrePolynomial_reduced χ m n k t hm hn hk hmred hnred hkred ht0 ht1)
      · rw [hroots]
        simp
      · rw [hroots]
        simp
      · rw [hroots]
        simp [Ne.symm ht0, Ne.symm ht1]
    · intro p _ _ χ P hχ hmonic hP hreduced hzero hone hfour
      exact h p χ P hχ hmonic hP hreduced hzero hone (by omega)
  · rintro ⟨hlegendre, hfour⟩ p _ _ χ P hχ hmonic hP hreduced hzero hone hthree
    by_cases hcard : P.roots.toFinset.card = 3
    · obtain ⟨t, ht0, ht1, hrootset⟩ :=
        exists_third_primeKummer_root P hzero hone hcard
      let m := P.rootMultiplicity 0
      let n := P.rootMultiplicity 1
      let k := P.rootMultiplicity t
      have htmem : t ∈ P.roots.toFinset := by
        rw [hrootset]
        simp
      have hm : 0 < m := by
        dsimp [m]
        rw [← Polynomial.count_roots]
        exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzero)
      have hn : 0 < n := by
        dsimp [n]
        rw [← Polynomial.count_roots]
        exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hone)
      have hk : 0 < k := by
        dsimp [k]
        rw [← Polynomial.count_roots]
        exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp htmem)
      have hmred : m < orderOf χ := hreduced 0 hzero
      have hnred : n < orderOf χ := hreduced 1 hone
      have hkred : k < orderOf χ := hreduced t htmem
      have hEq : P = primeKummerLegendrePolynomial m n k t := by
        dsimp [m, n, k]
        exact eq_primeKummerLegendrePolynomial_of_threeRoots P t ht0 ht1 hP hmonic hrootset
      by_cases hdegree : orderOf χ ∣ P.natDegree
      · have hnot : ¬orderOf χ ∣ P.rootMultiplicity 0 := by
          intro hdvd
          have hle := Nat.le_of_dvd hm hdvd
          omega
        exact exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_degree_dvd
          p χ P 0 hP hnot hdegree hcard
      · have hsum : ¬orderOf χ ∣ m + n + k := by
          intro hdvd
          apply hdegree
          rw [hEq, primeKummerLegendrePolynomial_natDegree]
          exact hdvd
        rw [hEq]
        exact hlegendre p χ m n k t hχ hm hn hk hmred hnred hkred
          ht0 ht1 hsum
    · exact hfour p χ P hχ hmonic hP hreduced hzero hone (by omega)

theorem TaoPrimeKummerLegendreOrFourRootsFrobeniusSystem.toFull
    (h : TaoPrimeKummerLegendreOrFourRootsFrobeniusSystem) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemThreeRootsOrMore.toFull
    (taoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemThreeRootsOrMore_iff_legendreOrFourRoots.mpr h)

end
end Tao2026



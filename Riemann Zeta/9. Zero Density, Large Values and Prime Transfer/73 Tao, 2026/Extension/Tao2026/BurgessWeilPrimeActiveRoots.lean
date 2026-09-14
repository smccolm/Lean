import Tao2026.BurgessWeilPrimeLowRoots

/-!
# Active-root reduction for the prime Burgess sum

A root whose multiplicity is divisible by the character order contributes one
away from that root and only forces the summand to vanish at the root itself.
This module separates those inactive roots exactly.  Their omitted zero-locus
cost is at most their cardinality and is absorbed by the existing
`2 * #roots * sqrt p` target.  The Jacobi-sum proof from
`BurgessWeilPrimeLowRoots` therefore handles every polynomial with at most two
active roots, even when the polynomial has many distinct roots.

Consequently the remaining Weil input may be restricted to polynomials with
at least three roots whose multiplicities are nonzero modulo `orderOf χ`.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def primeActiveRoots (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : Finset (ZMod p) :=
  P.roots.toFinset.filter fun a => ¬orderOf χ ∣ P.roots.count a

def primeInactiveRoots (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : Finset (ZMod p) :=
  P.roots.toFinset.filter fun a => orderOf χ ∣ P.roots.count a

theorem primeActiveRoots_union_primeInactiveRoots
    (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) :
    primeActiveRoots p χ P ∪ primeInactiveRoots p χ P = P.roots.toFinset := by
  ext a
  simp only [Finset.mem_union, primeActiveRoots, primeInactiveRoots,
    Finset.mem_filter]
  constructor
  · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
  · intro ha
    by_cases hdiv : orderOf χ ∣ P.roots.count a
    · exact Or.inr ⟨ha, hdiv⟩
    · exact Or.inl ⟨ha, hdiv⟩

theorem primeActiveRoots_subset_roots
    (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) :
    primeActiveRoots p χ P ⊆ P.roots.toFinset := by
  exact Finset.filter_subset _ _

theorem primeInactiveRoots_subset_roots
    (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) :
    primeInactiveRoots p χ P ⊆ P.roots.toFinset := by
  exact Finset.filter_subset _ _

/-- If the polynomial's total degree is divisible by the character order, so
is the sum of the active root multiplicities. -/
theorem orderOf_dvd_sum_primeActiveRoots_count
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree) :
    orderOf χ ∣ ∑ a ∈ primeActiveRoots p χ P, P.roots.count a := by
  have hdisjoint :
      Disjoint (primeActiveRoots p χ P) (primeInactiveRoots p χ P) := by
    rw [Finset.disjoint_left]
    intro a haActive haInactive
    exact (Finset.mem_filter.mp haActive).2
      (Finset.mem_filter.mp haInactive).2
  have hsum :
      (∑ a ∈ P.roots.toFinset, P.roots.count a) =
        (∑ a ∈ primeActiveRoots p χ P, P.roots.count a) +
          ∑ a ∈ primeInactiveRoots p χ P, P.roots.count a := by
    rw [← primeActiveRoots_union_primeInactiveRoots p χ P,
      Finset.sum_union hdisjoint]
  have hsumAll :
      (∑ a ∈ P.roots.toFinset, P.roots.count a) = P.natDegree := by
    rw [Multiset.toFinset_sum_count_eq, ← hP.natDegree_eq_card_roots]
  have hInactive :
      orderOf χ ∣
        ∑ a ∈ primeInactiveRoots p χ P, P.roots.count a :=
    Finset.dvd_sum fun a ha => (Finset.mem_filter.mp ha).2
  apply (Nat.dvd_add_iff_left hInactive).mpr
  rw [← hsum, hsumAll]
  exact hdegree

theorem primeRootProduct_eq_zero_of_mem_inactive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (x : ZMod p) (hx : x ∈ primeInactiveRoots p χ P) :
    (∏ a ∈ P.roots.toFinset, χ (x - a) ^ P.roots.count a) = 0 := by
  have hxroot : x ∈ P.roots.toFinset :=
    (Finset.mem_filter.mp hx).1
  have hcount : P.roots.count x ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hxroot)).ne'
  apply Finset.prod_eq_zero hxroot
  rw [sub_self, χ.map_zero, zero_pow hcount]

theorem primeRootProduct_eq_active_of_not_mem_inactive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (x : ZMod p) (hx : x ∉ primeInactiveRoots p χ P) :
    (∏ a ∈ P.roots.toFinset, χ (x - a) ^ P.roots.count a) =
      ∏ a ∈ primeActiveRoots p χ P, χ (x - a) ^ P.roots.count a := by
  symm
  apply Finset.prod_subset (primeActiveRoots_subset_roots p χ P)
  intro a haRoot haNotActive
  have hcount : P.roots.count a ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haRoot)).ne'
  have hdvd : orderOf χ ∣ P.roots.count a := by
    by_contra hnot
    exact haNotActive (Finset.mem_filter.mpr ⟨haRoot, hnot⟩)
  have hxa : x ≠ a := by
    intro h
    subst a
    exact hx (Finset.mem_filter.mpr ⟨haRoot, hdvd⟩)
  rw [← MulChar.pow_apply' χ hcount,
    orderOf_dvd_iff_pow_eq_one.mp hdvd]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxa))

def primeActiveRootCharacterSum (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : ℂ :=
  ∑ x : ZMod p, ∏ a ∈ primeActiveRoots p χ P,
    χ (x - a) ^ P.roots.count a

theorem sum_primeRootProduct_eq_filter_primeActiveRootProduct
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    (∑ x : ZMod p, ∏ a ∈ P.roots.toFinset,
        χ (x - a) ^ P.roots.count a) =
      ∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
          x ∉ primeInactiveRoots p χ P),
        ∏ a ∈ primeActiveRoots p χ P,
          χ (x - a) ^ P.roots.count a := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hmem : x ∈ primeInactiveRoots p χ P
  · rw [if_neg (not_not.mpr hmem),
      primeRootProduct_eq_zero_of_mem_inactive p χ P x hmem]
  · rw [if_pos hmem,
      primeRootProduct_eq_active_of_not_mem_inactive p χ P x hmem]

theorem norm_primeActiveRootCharacterSum_le_sqrt_of_card_le_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hcard : (primeActiveRoots p χ P).card ≤ 2) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ Real.sqrt p := by
  have hnot' : ¬orderOf χ ∣ P.roots.count a := by
    intro hdvd
    exact hnot ((Polynomial.count_roots P) ▸ hdvd)
  have hcountA : P.roots.count a ≠ 0 := by
    intro hzero
    apply hnot'
    rw [hzero]
    exact dvd_zero _
  have haRoot : a ∈ P.roots.toFinset :=
    Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcountA))
  have haActive : a ∈ primeActiveRoots p χ P :=
    Finset.mem_filter.mpr ⟨haRoot, hnot'⟩
  have hcardPos : 0 < (primeActiveRoots p χ P).card :=
    Finset.card_pos.mpr ⟨a, haActive⟩
  have hcases : (primeActiveRoots p χ P).card = 1 ∨
      (primeActiveRoots p χ P).card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hone
    have hac : a = c := by simpa [hc] using haActive
    subst c
    have hpow : χ ^ P.roots.count a ≠ 1 := by
      intro heq
      exact hnot' (orderOf_dvd_iff_pow_eq_one.mpr heq)
    have hsum : primeActiveRootCharacterSum p χ P = 0 := by
      unfold primeActiveRootCharacterSum
      rw [hc]
      simp only [Finset.prod_singleton]
      calc
        ∑ x : ZMod p, χ (x - a) ^ P.roots.count a =
            ∑ x : ZMod p, (χ ^ P.roots.count a) (x - a) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [MulChar.pow_apply' χ hcountA]
        _ = ∑ x : ZMod p, (χ ^ P.roots.count a) x :=
          Equiv.sum_comp (Equiv.subRight a)
            (fun x : ZMod p => (χ ^ P.roots.count a) x)
        _ = 0 := MulChar.sum_eq_zero_of_ne_one hpow
    rw [hsum, norm_zero]
    exact Real.sqrt_nonneg _
  · obtain ⟨u, v, huv, huvRoots⟩ := Finset.card_eq_two.mp htwo
    have huActive : u ∈ primeActiveRoots p χ P := by simp [huvRoots]
    have hvActive : v ∈ primeActiveRoots p χ P := by simp [huvRoots]
    have huRoot : u ∈ P.roots.toFinset :=
      primeActiveRoots_subset_roots p χ P huActive
    have hvRoot : v ∈ P.roots.toFinset :=
      primeActiveRoots_subset_roots p χ P hvActive
    let m := P.roots.count u
    let n := P.roots.count v
    have hm : m ≠ 0 :=
      (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
    have hn : n ≠ 0 :=
      (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
    have hpow : χ ^ m ≠ 1 := by
      intro heq
      have hdvd : orderOf χ ∣ m := orderOf_dvd_iff_pow_eq_one.mpr heq
      have hnotU : ¬orderOf χ ∣ P.roots.count u :=
        (Finset.mem_filter.mp huActive).2
      exact hnotU hdvd
    unfold primeActiveRootCharacterSum
    rw [huvRoots]
    have hsum :
        (∑ x : ZMod p, ∏ c ∈ ({u, v} : Finset (ZMod p)),
          χ (x - c) ^ P.roots.count c) =
        (χ ^ m) (v - u) * (χ ^ n) (u - v) *
          jacobiSum (χ ^ m) (χ ^ n) := by
      calc
        (∑ x : ZMod p, ∏ c ∈ ({u, v} : Finset (ZMod p)),
            χ (x - c) ^ P.roots.count c) =
            ∑ x : ZMod p, χ (x - u) ^ m * χ (x - v) ^ n := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [huv, m, n]
        _ = _ := twoRootCharacterSum_eq_jacobiSum p χ u v huv m n hm hn
    rw [hsum]
    simp only [norm_mul]
    calc
      ‖(χ ^ m) (v - u)‖ * ‖(χ ^ n) (u - v)‖ *
            ‖jacobiSum (χ ^ m) (χ ^ n)‖ ≤
          1 * 1 * ‖jacobiSum (χ ^ m) (χ ^ n)‖ := by
        gcongr
        · exact DirichletCharacter.norm_le_one (χ ^ m) (v - u)
        · exact DirichletCharacter.norm_le_one (χ ^ n) (u - v)
      _ ≤ Real.sqrt p := by
        simpa using norm_jacobiSum_le_sqrt_prime p (χ ^ m) (χ ^ n) hpow

theorem norm_primeActiveRootProduct_le_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (x : ZMod p) :
    ‖∏ a ∈ primeActiveRoots p χ P,
        χ (x - a) ^ P.roots.count a‖ ≤ 1 := by
  simp only [norm_prod, norm_pow]
  apply Finset.prod_le_one
  · intro a ha
    positivity
  · intro a ha
    exact pow_le_one₀ (norm_nonneg _)
      (DirichletCharacter.norm_le_one χ (x - a))

theorem norm_filter_primeActiveRootProduct_le
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hcard : (primeActiveRoots p χ P).card ≤ 2) :
    ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
        x ∉ primeInactiveRoots p χ P),
      ∏ b ∈ primeActiveRoots p χ P,
        χ (x - b) ^ P.roots.count b‖ ≤
      Real.sqrt p + (primeInactiveRoots p χ P).card := by
  let f : ZMod p → ℂ := fun x =>
    ∏ b ∈ primeActiveRoots p χ P,
      χ (x - b) ^ P.roots.count b
  let I := primeInactiveRoots p χ P
  have hsplit :
      (∑ x ∈ I, f x) +
          (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        ∑ x : ZMod p, f x := by
    simpa [I] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x : ZMod p => x ∈ I) f)
  have hrewrite :
      (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        (∑ x : ZMod p, f x) - ∑ x ∈ I, f x := by
    linear_combination hsplit
  have htotal : ‖∑ x : ZMod p, f x‖ ≤ Real.sqrt p := by
    simpa [f, primeActiveRootCharacterSum] using
      norm_primeActiveRootCharacterSum_le_sqrt_of_card_le_two
        p χ P a hnot hcard
  have hbad : ‖∑ x ∈ I, f x‖ ≤ I.card := by
    calc
      ‖∑ x ∈ I, f x‖ ≤ ∑ x ∈ I, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ I, (1 : ℝ) := by
        exact Finset.sum_le_sum fun x hx => by
          simpa [f] using norm_primeActiveRootProduct_le_one p χ P x
      _ = I.card := by simp
  change ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x‖ ≤ _
  rw [hrewrite]
  exact (norm_sub_le _ _).trans (add_le_add htotal hbad)

theorem primeSplitPolynomialWeilBound_of_card_activeRoots_le_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hcard : (primeActiveRoots p χ P).card ≤ 2) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hrestricted := norm_filter_primeActiveRootProduct_le
    p χ P a hnot hcard
  have hmult : 0 < P.rootMultiplicity a := by
    by_contra hzero
    have heq : P.rootMultiplicity a = 0 := Nat.eq_zero_of_not_pos hzero
    apply hnot
    rw [heq]
    exact dvd_zero _
  have haRoot : a ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, ← Multiset.count_pos,
      Polynomial.count_roots]
    exact hmult
  have hrootCard : 1 ≤ P.roots.toFinset.card :=
    Finset.one_le_card.mpr ⟨a, haRoot⟩
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hp : p.Prime := Fact.out
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hp.one_le
  have hroom :
      Real.sqrt p + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (1 : ℝ) ≤ P.roots.toFinset.card := by
      exact_mod_cast hrootCard
    push_cast
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ Real.sqrt p + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

def TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) (a : ZMod p),
    χ ≠ 1 → P.Splits →
    ¬orderOf χ ∣ P.rootMultiplicity a →
    3 ≤ (primeActiveRoots p χ P).card →
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p

theorem TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore.toFull
    (hweil : TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore) :
    TaoPrimeSplitPolynomialWeilBound := by
  intro p _ _ χ P a hχ hP hnot
  by_cases hcard : (primeActiveRoots p χ P).card ≤ 2
  · exact primeSplitPolynomialWeilBound_of_card_activeRoots_le_two
      p χ P a hχ hP hnot hcard
  · exact hweil p χ P a hχ hP hnot (by omega)

theorem TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore.toComposite
    (hweil : TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toFull.toComposite

end

end Tao2026

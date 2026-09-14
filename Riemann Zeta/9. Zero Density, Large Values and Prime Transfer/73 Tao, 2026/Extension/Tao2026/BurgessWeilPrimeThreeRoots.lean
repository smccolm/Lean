import Tao2026.BurgessWeilPrimeActiveRoots

/-!
# The three-active-root prime Burgess sum

When a split polynomial has degree divisible by the character order, the sum
of its active root multiplicities is divisible by that order.  For exactly
three active roots, a fractional-linear change of variables sends one root to
infinity.  The common denominator character cancels, leaving a two-root
Jacobi sum with one deleted point.  This gives the elementary bound
`sqrt p + 1`, and the existing Burgess target absorbs both the extra point and
the inactive-root correction.

Consequently the remaining prime Weil input for the cleared Burgess
polynomial may be restricted to at least four active roots.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def threeRootMobiusEquiv
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a c : ZMod p) (hac : a ≠ c) : ZMod p ≃ ZMod p where
  toFun x := if x = c then 1 else (x - a) / (x - c)
  invFun y := if y = 1 then c else (y * c - a) / (y - 1)
  left_inv := by
    intro x
    by_cases hx : x = c
    · simp [hx]
    · have hden : x - c ≠ 0 := sub_ne_zero.mpr hx
      have hy : (x - a) / (x - c) ≠ 1 := by
        intro h
        rw [div_eq_one_iff_eq hden] at h
        exact hac (sub_right_inj.mp h)
      simp only [hx, ↓reduceIte, hy]
      rw [div_eq_iff (sub_ne_zero.mpr hy)]
      field_simp [hden]
      ring

  right_inv := by
    intro y
    by_cases hy : y = 1
    · simp [hy]
    · have hden : y - 1 ≠ 0 := sub_ne_zero.mpr hy
      have hx : (y * c - a) / (y - 1) ≠ c := by
        intro h
        rw [div_eq_iff hden] at h
        apply hac
        linear_combination -h
      simp only [hy, ↓reduceIte, hx]
      rw [div_eq_iff (sub_ne_zero.mpr hx)]
      field_simp [hden]
      ring

@[simp] theorem threeRootMobiusEquiv_symm_apply
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a c y : ZMod p) (hac : a ≠ c) :
    (threeRootMobiusEquiv p a c hac).symm y =
      if y = 1 then c else (y * c - a) / (y - 1) := rfl

theorem twoRootMulCharSum_eq_jacobiSum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β : MulChar (ZMod p) ℂ) (a b : ZMod p) (hab : a ≠ b) :
    (∑ x : ZMod p, α (x - a) * β (x - b)) =
      α (b - a) * β (a - b) * jacobiSum α β := by
  let d : ZMod p := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  let e : Equiv (ZMod p) (ZMod p) :=
    (Equiv.mulLeft₀ d hd).trans (Equiv.addRight a)
  calc
    (∑ x : ZMod p, α (x - a) * β (x - b)) =
        ∑ y : ZMod p, α (e y - a) * β (e y - b) :=
      (Equiv.sum_comp e
        (fun x : ZMod p => α (x - a) * β (x - b))).symm
    _ = α d * β (-d) * jacobiSum α β := by
      unfold jacobiSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have hleft : e y - a = d * y := by simp [e]
      have hright : e y - b = (-d) * (1 - y) := by
        dsimp [e]
        dsimp [d]
        ring
      rw [hleft, hright, map_mul, map_mul]
      ring
    _ = _ := by simp [d, neg_sub]

theorem threeRootMobius_term
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ : MulChar (ZMod p) ℂ) (hprod : α * β * γ = 1)
    (a b c : ZMod p) (hac : a ≠ c) (hbc : b ≠ c)
    (y : ZMod p) (hy : y ≠ 1) :
    let e := threeRootMobiusEquiv p a c hac
    let lam := (a - b) / (c - b)
    α (e.symm y - a) * β (e.symm y - b) * γ (e.symm y - c) =
      (α (c - a) * β (c - b) * γ (c - a)) *
        (α y * β (y - lam)) := by
  dsimp only
  rw [threeRootMobiusEquiv_symm_apply, if_neg hy]
  have hden : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have hxa : (y * c - a) / (y - 1) - a =
      y * (c - a) / (y - 1) := by field_simp; ring
  have hxb : (y * c - a) / (y - 1) - b =
      (c - b) * (y - (a - b) / (c - b)) / (y - 1) := by
    field_simp
    ring
  have hxc : (y * c - a) / (y - 1) - c =
      (c - a) / (y - 1) := by field_simp; ring
  rw [hxa, hxb, hxc]
  have hmapdivα (u v : ZMod p) : α (u / v) = α u / α v := by
    exact map_div₀ α.toMonoidWithZeroHom u v
  have hmapdivβ (u v : ZMod p) : β (u / v) = β u / β v := by
    exact map_div₀ β.toMonoidWithZeroHom u v
  have hmapdivγ (u v : ZMod p) : γ (u / v) = γ u / γ v := by
    exact map_div₀ γ.toMonoidWithZeroHom u v
  rw [hmapdivα, map_mul, hmapdivβ, map_mul, hmapdivγ]
  have hcancel : α (y - 1) * β (y - 1) * γ (y - 1) = 1 := by
    rw [← MulChar.mul_apply, ← MulChar.mul_apply, hprod]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hden)
  have hα : α (y - 1) ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hβ : β (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hγ : γ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcancel
    exact zero_ne_one hcancel
  field_simp [hα, hβ, hγ]
  linear_combination
    -(α y * α (c - a) * β (c - b) *
      β ((y * (c - b) - (a - b)) / (c - b)) * γ (c - a)) * hcancel

theorem norm_twoRootMulCharSum_le_sqrt_prime
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β : MulChar (ZMod p) ℂ) (hα : α ≠ 1)
    (a b : ZMod p) (hab : a ≠ b) :
    ‖∑ x : ZMod p, α (x - a) * β (x - b)‖ ≤ Real.sqrt p := by
  rw [twoRootMulCharSum_eq_jacobiSum p α β a b hab]
  simp only [norm_mul]
  calc
    ‖α (b - a)‖ * ‖β (a - b)‖ * ‖jacobiSum α β‖ ≤
        1 * 1 * ‖jacobiSum α β‖ := by
      gcongr
      · exact DirichletCharacter.norm_le_one α (b - a)
      · exact DirichletCharacter.norm_le_one β (a - b)
    _ ≤ Real.sqrt p := by
      simpa using norm_jacobiSum_le_sqrt_prime p α β hα

theorem threeRootMulCharSum_eq_twoRootSum_sub
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ : MulChar (ZMod p) ℂ) (hprod : α * β * γ = 1)
    (a b c : ZMod p) (hac : a ≠ c) (hbc : b ≠ c) :
    let lam := (a - b) / (c - b)
    (∑ x : ZMod p, α (x - a) * β (x - b) * γ (x - c)) =
      (α (c - a) * β (c - b) * γ (c - a)) *
        ((∑ y : ZMod p, α y * β (y - lam)) - β (1 - lam)) := by
  dsimp only
  let e := threeRootMobiusEquiv p a c hac
  let f : ZMod p → ℂ := fun x =>
    α (x - a) * β (x - b) * γ (x - c)
  let g : ZMod p → ℂ := fun y =>
    α y * β (y - (a - b) / (c - b))
  let C : ℂ := α (c - a) * β (c - b) * γ (c - a)
  have hone : f (e.symm 1) = 0 := by
    simp [f, e, γ.map_zero]
  have hterm (y : ZMod p) (hy : y ∈ Finset.univ.erase 1) :
      f (e.symm y) = C * g y := by
    have hyOne : y ≠ 1 := by simpa using hy
    simpa [f, g, C, e] using
      threeRootMobius_term p α β γ hprod a b c hac hbc y hyOne
  calc
    (∑ x : ZMod p, α (x - a) * β (x - b) * γ (x - c)) =
        ∑ x : ZMod p, f x := by rfl
    _ = ∑ y : ZMod p, f (e.symm y) :=
      (Equiv.sum_comp e.symm f).symm
    _ = ∑ y ∈ Finset.univ.erase 1, f (e.symm y) := by
      exact (Finset.sum_erase (s := Finset.univ)
        (f := fun y => f (e.symm y)) hone).symm
    _ = C * ∑ y ∈ Finset.univ.erase 1, g y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      exact hterm
    _ = C * ((∑ y : ZMod p, g y) - g 1) := by
      congr 1
      have h := Finset.sum_erase_add Finset.univ g
        (Finset.mem_univ (1 : ZMod p))
      linear_combination h
    _ = _ := by simp [C, g, MulChar.map_one]

theorem norm_threeRootMulCharSum_le_sqrt_add_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ : MulChar (ZMod p) ℂ) (hα : α ≠ 1)
    (hprod : α * β * γ = 1)
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ‖∑ x : ZMod p, α (x - a) * β (x - b) * γ (x - c)‖ ≤
      Real.sqrt p + 1 := by
  let lam : ZMod p := (a - b) / (c - b)
  have hlam : lam ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hbc.symm)
  rw [threeRootMulCharSum_eq_twoRootSum_sub p α β γ hprod a b c hac hbc]
  simp only [norm_mul]
  have hC :
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ ≤ 1 := by
    calc
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ ≤
          1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one α (c - a)
        · exact DirichletCharacter.norm_le_one β (c - b)
        · exact DirichletCharacter.norm_le_one γ (c - a)
      _ = 1 := by norm_num
  have htwo :
      ‖∑ y : ZMod p, α y * β (y - lam)‖ ≤ Real.sqrt p := by
    simpa using norm_twoRootMulCharSum_le_sqrt_prime
      p α β hα 0 lam hlam.symm
  have hdeleted : ‖β (1 - lam)‖ ≤ 1 :=
    DirichletCharacter.norm_le_one β (1 - lam)
  calc
    (‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖) *
          ‖(∑ y : ZMod p, α y * β (y - lam)) - β (1 - lam)‖ ≤
        1 * ‖(∑ y : ZMod p, α y * β (y - lam)) - β (1 - lam)‖ := by
      gcongr
    _ ≤ ‖∑ y : ZMod p, α y * β (y - lam)‖ + ‖β (1 - lam)‖ := by
      simpa using norm_sub_le
        (∑ y : ZMod p, α y * β (y - lam)) (β (1 - lam))
    _ ≤ Real.sqrt p + 1 := add_le_add htwo hdeleted

theorem norm_primeActiveRootCharacterSum_le_sqrt_add_one_of_card_eq_three
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 3) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ Real.sqrt p + 1 := by
  obtain ⟨u, v, w, huv, huw, hvw, hroots⟩ := Finset.card_eq_three.mp hcard
  have huActive : u ∈ primeActiveRoots p χ P := by simp [hroots]
  have hvActive : v ∈ primeActiveRoots p χ P := by simp [hroots]
  have hwActive : w ∈ primeActiveRoots p χ P := by simp [hroots]
  have huRoot : u ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P huActive
  have hvRoot : v ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hvActive
  have hwRoot : w ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hwActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hmActive : ¬orderOf χ ∣ m := (Finset.mem_filter.mp huActive).2
  have hpow : χ ^ m ≠ 1 := by
    intro heq
    exact hmActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count
    p χ P hP hdegree
  have hmnk : orderOf χ ∣ m + n + k := by
    simpa [hroots, huv, huw, hvw, m, n, k, add_assoc, add_comm,
      add_left_comm] using hsum
  have hprod : (χ ^ m) * (χ ^ n) * (χ ^ k) = 1 := by
    rw [← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnk
  have hthree := norm_threeRootMulCharSum_le_sqrt_add_one
    p (χ ^ m) (χ ^ n) (χ ^ k) hpow hprod
      u v w huv huw hvw
  unfold primeActiveRootCharacterSum
  rw [hroots]
  convert hthree using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x hx
  simp [huv, huw, hvw]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk]
  simp [m, n, k, Polynomial.count_roots]
  ac_rfl

theorem norm_filter_primeActiveRootProduct_le_of_card_eq_three_degree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 3) :
    ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
        x ∉ primeInactiveRoots p χ P),
      ∏ b ∈ primeActiveRoots p χ P,
        χ (x - b) ^ P.roots.count b‖ ≤
      Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
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
  have htotal : ‖∑ x : ZMod p, f x‖ ≤ Real.sqrt p + 1 := by
    simpa [f, primeActiveRootCharacterSum] using
      norm_primeActiveRootCharacterSum_le_sqrt_add_one_of_card_eq_three
        p χ P hP hdegree hcard
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

theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_three_degree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 3) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_card_eq_three_degree
      p χ P hP hdegree hcard
  have hrootCard : 3 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hp : p.Prime := Fact.out
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hp.one_le
  have hroom :
      Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (3 : ℝ) ≤ P.roots.toFinset.card := by
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
    _ ≤ Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

def TaoPrimeSplitPolynomialWeilBoundDegreeDivisible : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) (a : ZMod p),
    χ ≠ 1 → P.Splits →
    ¬orderOf χ ∣ P.rootMultiplicity a →
    orderOf χ ∣ P.natDegree →
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p

def TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) (a : ZMod p),
    χ ≠ 1 → P.Splits →
    ¬orderOf χ ∣ P.rootMultiplicity a →
    orderOf χ ∣ P.natDegree →
    4 ≤ (primeActiveRoots p χ P).card →
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p

theorem TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore.toDegreeDivisible
    (hweil : TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore) :
    TaoPrimeSplitPolynomialWeilBoundDegreeDivisible := by
  intro p _ _ χ P a hχ hP hnot hdegree
  by_cases hcardTwo : (primeActiveRoots p χ P).card ≤ 2
  · exact primeSplitPolynomialWeilBound_of_card_activeRoots_le_two
      p χ P a hχ hP hnot hcardTwo
  · by_cases hcardThree : (primeActiveRoots p χ P).card = 3
    · exact primeSplitPolynomialWeilBound_of_card_activeRoots_eq_three_degree
        p χ P a hχ hP hnot hdegree hcardThree
    · exact hweil p χ P a hχ hP hnot hdegree (by omega)

theorem TaoPrimeSplitPolynomialWeilBoundDegreeDivisible.toLinearQuotient
    (hweil : TaoPrimeSplitPolynomialWeilBoundDegreeDivisible) :
    TaoPrimeLinearQuotientWeilBound := by
  intro p r _ χ b j hp hr hχ hunique
  letI : Fact p.Prime := ⟨hp⟩
  rw [primeLinearQuotientCorrelation_eq_polynomial p r χ b hχ]
  calc
    ‖primePolynomialCharacterCorrelation p χ
        (primeLinearOrderPolynomial p r χ b)‖ ≤
        ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
          Real.sqrt p :=
      hweil p χ (primeLinearOrderPolynomial p r χ b) (-b j)
        hχ (primeLinearOrderPolynomial_splits p r χ b)
        (not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
          p r hp χ b j hχ hunique)
        (orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b)
    _ ≤ ((4 * r : ℕ) : ℝ) * Real.sqrt p := by
      have hcard := card_roots_primeLinearOrderPolynomial_le p r hp χ b hχ
      have hnat :
          2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ≤
            4 * r := by omega
      have hreal :
          ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) ≤
            ((4 * r : ℕ) : ℝ) := by exact_mod_cast hnat
      exact mul_le_mul_of_nonneg_right hreal (Real.sqrt_nonneg p)

theorem TaoPrimeSplitPolynomialWeilBoundDegreeDivisible.toComposite
    (hweil : TaoPrimeSplitPolynomialWeilBoundDegreeDivisible) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toLinearQuotient.toComposite

theorem TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore.toComposite
    (hweil : TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toDegreeDivisible.toComposite

end


end Tao2026

import Tao2026.BurgessWeilPrimePolynomial
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# The one- and two-root prime Burgess sums

The standard split-polynomial Weil boundary has elementary low-root cases.
A polynomial with one distinct root gives a translated complete sum of a
nontrivial multiplicative character, hence zero.  With two distinct roots an
affine change of variables identifies the sum with a Jacobi sum.  Mathlib's
Gauss-sum identity then gives the square-root bound.

Consequently the remaining Weil input may be restricted, without loss, to
split polynomials with at least three distinct roots.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Complex conjugation inverts both characters in a Jacobi sum. -/
theorem star_jacobiSum {F : Type*} [Field F] [Fintype F]
    (χ φ : MulChar F ℂ) :
    star (jacobiSum χ φ) = jacobiSum χ⁻¹ φ⁻¹ := by
  unfold jacobiSum
  change (starRingEnd ℂ) (∑ x : F, χ x * φ (1 - x)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  change star (χ x * φ (1 - x)) = _
  rw [star_mul, MulChar.star_apply', MulChar.star_apply', mul_comm]

/-- When all three characters are nontrivial, the norm of a complex Jacobi
sum is the square root of the field cardinality. -/
theorem norm_jacobiSum_eq_sqrt_card {F : Type*} [Field F] [Fintype F]
    (hring : ringChar ℂ ≠ ringChar F)
    (χ φ : MulChar F ℂ) (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ = Real.sqrt (Fintype.card F) := by
  rw [Complex.norm_def]
  congr 1
  have hstar : star (jacobiSum χ φ) = jacobiSum χ⁻¹ φ⁻¹ :=
    star_jacobiSum χ φ
  have hprod := jacobiSum_mul_jacobiSum_inv hring hχ hφ hχφ
  have hsquareC :
      (Complex.normSq (jacobiSum χ φ) : ℂ) =
        (Fintype.card F : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    change star (jacobiSum χ φ) * jacobiSum χ φ = _
    rw [hstar, mul_comm]
    exact hprod
  exact_mod_cast hsquareC

/-- Evaluate a split-polynomial character sum by grouping its root multiset
over the distinct roots. -/
theorem primePolynomialCharacterCorrelation_eq_rootProduct
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) :
    primePolynomialCharacterCorrelation p χ P =
      χ P.leadingCoeff *
        ∑ x : ZMod p, ∏ a ∈ P.roots.toFinset,
          χ (x - a) ^ P.roots.count a := by
  unfold primePolynomialCharacterCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hP.eval_eq_prod_roots, Finset.prod_multiset_map_count,
    map_mul, map_prod]
  simp only [map_pow]

/-- A split polynomial with one distinct root and a nontrivial character
exponent has complete character sum zero. -/
theorem primeSplitPolynomialCorrelation_eq_zero_of_single_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hroots : P.roots.toFinset = {a}) :
    primePolynomialCharacterCorrelation p χ P = 0 := by
  let m := P.roots.count a
  have hnot' : ¬orderOf χ ∣ m := by
    intro hdvd
    apply hnot
    exact (Polynomial.count_roots P) ▸ hdvd
  have hm : m ≠ 0 := by
    intro hm0
    apply hnot'
    rw [hm0]
    exact dvd_zero _
  have hpow : χ ^ m ≠ 1 := by
    intro heq
    exact hnot' (orderOf_dvd_iff_pow_eq_one.mpr heq)
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP, hroots]
  simp only [prod_singleton]
  have hsum : ∑ x : ZMod p, χ (x - a) ^ m = 0 := by
    calc
      ∑ x : ZMod p, χ (x - a) ^ m =
          ∑ x : ZMod p, (χ ^ m) (x - a) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [MulChar.pow_apply' χ hm]
      _ = ∑ x : ZMod p, (χ ^ m) x :=
        Equiv.sum_comp (Equiv.subRight a) (fun x : ZMod p => (χ ^ m) x)
      _ = 0 := MulChar.sum_eq_zero_of_ne_one hpow
  rw [hsum, mul_zero]

/-- An affine change of variables turns the complete two-root character sum
into a Jacobi sum, including arbitrary positive root multiplicities. -/
theorem twoRootCharacterSum_eq_jacobiSum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (a b : ZMod p) (hab : a ≠ b)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (∑ x : ZMod p, χ (x - a) ^ m * χ (x - b) ^ n) =
      (χ ^ m) (b - a) * (χ ^ n) (a - b) *
        jacobiSum (χ ^ m) (χ ^ n) := by
  let d : ZMod p := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  let e : ZMod p ≃ ZMod p :=
    (Equiv.mulLeft₀ d hd).trans (Equiv.addRight a)
  calc
    (∑ x : ZMod p, χ (x - a) ^ m * χ (x - b) ^ n) =
        ∑ x : ZMod p, (χ ^ m) (x - a) * (χ ^ n) (x - b) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn]
    _ = ∑ y : ZMod p, (χ ^ m) (e y - a) * (χ ^ n) (e y - b) :=
      (Equiv.sum_comp e
        (fun x : ZMod p => (χ ^ m) (x - a) * (χ ^ n) (x - b))).symm
    _ = (χ ^ m) d * (χ ^ n) (-d) *
        jacobiSum (χ ^ m) (χ ^ n) := by
      unfold jacobiSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have hleft : e y - a = d * y := by
        simp [e]
      have hright : e y - b = (-d) * (1 - y) := by
        dsimp [e]
        dsimp [d]
        ring
      rw [hleft, hright, map_mul, map_mul]
      ring
    _ = _ := by simp [d, neg_sub]

/-- If the first character is nontrivial, every Jacobi sum over `ZMod p` has
norm at most `sqrt p`; the trivial-second and inverse-product cases have norm
at most one. -/
theorem norm_jacobiSum_le_sqrt_prime
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ φ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖jacobiSum χ φ‖ ≤ Real.sqrt p := by
  have hp : p.Prime := Fact.out
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact hpone
  by_cases hφ : φ = 1
  · subst φ
    rw [jacobiSum_comm, jacobiSum_one_nontrivial hχ]
    simpa using hsqrt
  by_cases hprod : χ * φ = 1
  · have hφinv : φ = χ⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [hφinv, jacobiSum_nontrivial_inv hχ]
    calc
      ‖-χ (-1)‖ = ‖χ (-1)‖ := norm_neg _
      _ ≤ 1 := DirichletCharacter.norm_le_one χ (-1)
      _ ≤ Real.sqrt p := hsqrt
  · exact le_of_eq (by
      simpa [ZMod.card] using
        (norm_jacobiSum_eq_sqrt_card
          (by simpa [ZMod.ringChar_zmod_n] using hp.ne_zero.symm)
          χ φ hχ hφ hprod))

/-- For a split polynomial with exactly two distinct roots, one nontrivial
root exponent already gives the sharper bound `sqrt p`. -/
theorem primeSplitPolynomialCorrelation_le_sqrt_of_two_roots
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hroots : P.roots.toFinset = {a, b}) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤ Real.sqrt p := by
  let m := P.roots.count a
  let n := P.roots.count b
  have haMem : a ∈ P.roots.toFinset := by simp [hroots]
  have hbMem : b ∈ P.roots.toFinset := by simp [hroots]
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haMem)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hbMem)).ne'
  have hnot' : ¬orderOf χ ∣ m := by
    intro hdvd
    apply hnot
    exact (Polynomial.count_roots P) ▸ hdvd
  have hpow : χ ^ m ≠ 1 := by
    intro heq
    exact hnot' (orderOf_dvd_iff_pow_eq_one.mpr heq)
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP, hroots]
  have hsum :
      (∑ x : ZMod p, ∏ c ∈ ({a, b} : Finset (ZMod p)),
        χ (x - c) ^ P.roots.count c) =
      (χ ^ m) (b - a) * (χ ^ n) (a - b) *
        jacobiSum (χ ^ m) (χ ^ n) := by
    calc
      (∑ x : ZMod p, ∏ c ∈ ({a, b} : Finset (ZMod p)),
          χ (x - c) ^ P.roots.count c) =
          ∑ x : ZMod p, χ (x - a) ^ m * χ (x - b) ^ n := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hab, m, n]
      _ = _ := twoRootCharacterSum_eq_jacobiSum p χ a b hab m n hm hn
  rw [hsum]
  simp only [norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          (‖(χ ^ m) (b - a)‖ * ‖(χ ^ n) (a - b)‖ *
            ‖jacobiSum (χ ^ m) (χ ^ n)‖) ≤
        1 * (1 * 1 * ‖jacobiSum (χ ^ m) (χ ^ n)‖) := by
      gcongr
      · exact DirichletCharacter.norm_le_one χ P.leadingCoeff
      · exact DirichletCharacter.norm_le_one (χ ^ m) (b - a)
      · exact DirichletCharacter.norm_le_one (χ ^ n) (a - b)
    _ ≤ Real.sqrt p := by
      simpa using norm_jacobiSum_le_sqrt_prime p (χ ^ m) (χ ^ n) hpow

/-- The split-polynomial Weil estimate is elementary whenever there are at
most two distinct roots. -/
theorem primeSplitPolynomialWeilBound_of_card_roots_le_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hcard : P.roots.toFinset.card ≤ 2) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hmult : 0 < P.rootMultiplicity a := by
    by_contra hzero
    have heq : P.rootMultiplicity a = 0 := Nat.eq_zero_of_not_pos hzero
    apply hnot
    rw [heq]
    exact dvd_zero _
  have haMem : a ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, ← Multiset.count_pos,
      Polynomial.count_roots]
    exact hmult
  have hcardPos : 0 < P.roots.toFinset.card := Finset.card_pos.mpr ⟨a, haMem⟩
  have hcases : P.roots.toFinset.card = 1 ∨
      P.roots.toFinset.card = 2 := by
    omega
  rcases hcases with hone | htwo
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hone
    have hac : a = c := by simpa [hc] using haMem
    subst c
    rw [primeSplitPolynomialCorrelation_eq_zero_of_single_root
      p χ P a hP hnot hc, norm_zero]
    positivity
  · obtain ⟨u, v, huv, huvRoots⟩ := Finset.card_eq_two.mp htwo
    have hauv : a = u ∨ a = v := by simpa [huvRoots] using haMem
    have hstrong :
        ‖primePolynomialCharacterCorrelation p χ P‖ ≤ Real.sqrt p := by
      rcases hauv with rfl | rfl
      · exact primeSplitPolynomialCorrelation_le_sqrt_of_two_roots
          p χ P a v huv hP hnot huvRoots
      · exact primeSplitPolynomialCorrelation_le_sqrt_of_two_roots
          p χ P a u huv.symm hP hnot (by
            simpa [Finset.pair_comm] using huvRoots)
    calc
      ‖primePolynomialCharacterCorrelation p χ P‖ ≤ Real.sqrt p := hstrong
      _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
        rw [htwo]
        norm_num
        nlinarith [Real.sqrt_nonneg (p : ℝ)]

/-- The genuine residual Weil contract after removing the complete one- and
two-root Jacobi-sum cases. -/
def TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) (a : ZMod p),
    χ ≠ 1 → P.Splits →
    ¬orderOf χ ∣ P.rootMultiplicity a →
    3 ≤ P.roots.toFinset.card →
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p

/-- A Weil theorem restricted to at least three distinct roots supplies the
full split-polynomial boundary. -/
theorem TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore.toFull
    (hweil : TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore) :
    TaoPrimeSplitPolynomialWeilBound := by
  intro p _ _ χ P a hχ hP hnot
  by_cases hcard : P.roots.toFinset.card ≤ 2
  · exact primeSplitPolynomialWeilBound_of_card_roots_le_two
      p χ P a hχ hP hnot hcard
  · exact hweil p χ P a hχ hP hnot (by omega)

/-- The residual three-or-more-root Weil theorem is sufficient for the full
cube-free composite Burgess complete-sum predicate. -/
theorem TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore.toComposite
    (hweil : TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toFull.toComposite

end

end Tao2026

import Tao2026.BurgessWeilPrimeKummerActivePolynomial

/-!
# Reduced active Kummer polynomials

Active multiplicities matter to a Kummer character only modulo the character
order.  This file replaces every retained multiplicity by its nonzero least
residue, proving that the complete norm-lifted trace sequence is unchanged.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The canonical active polynomial with every exponent reduced modulo the
order of the source character. -/
def primeReducedActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    Polynomial (ZMod p) :=
  C P.leadingCoeff *
    ∏ a ∈ primeActiveRoots p χ P,
      (X - C a) ^ (P.rootMultiplicity a % orderOf χ)

/-- An active multiplicity has nonzero residue modulo the character order. -/
theorem rootMultiplicity_mod_orderOf_ne_zero_of_mem_primeActiveRoots
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    {a : ZMod p} (ha : a ∈ primeActiveRoots p χ P) :
    P.rootMultiplicity a % orderOf χ ≠ 0 := by
  intro hzero
  have hdiv : orderOf χ ∣ P.rootMultiplicity a :=
    Nat.dvd_of_mod_eq_zero hzero
  have hnot := (Finset.mem_filter.mp ha).2
  rw [Polynomial.count_roots] at hnot
  exact hnot hdiv

/-- Evaluation of the reduced active polynomial after arbitrary scalar
extension. -/
theorem eval_map_primeReducedActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    {L : Type*} [Field L] [Algebra (ZMod p) L] (x : L) :
    ((primeReducedActiveRootPolynomial p χ P).map
        (algebraMap (ZMod p) L)).eval x =
      algebraMap (ZMod p) L P.leadingCoeff *
        ∏ a ∈ primeActiveRoots p χ P,
          (x - algebraMap (ZMod p) L a) ^
            (P.rootMultiplicity a % orderOf χ) := by
  rw [Polynomial.eval_map]
  change (Polynomial.eval₂RingHom (algebraMap (ZMod p) L) x)
      (C P.leadingCoeff *
        ∏ a ∈ primeActiveRoots p χ P,
          (X - C a) ^ (P.rootMultiplicity a % orderOf χ)) = _
  rw [map_mul]
  have hC :
      (Polynomial.eval₂RingHom (algebraMap (ZMod p) L) x)
          (C P.leadingCoeff) =
        algebraMap (ZMod p) L P.leadingCoeff := by
    change Polynomial.eval₂ (algebraMap (ZMod p) L) x
      (C P.leadingCoeff) = _
    exact Polynomial.eval₂_C _ _
  rw [hC, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  simp

/-- The reduced active polynomial is nonzero whenever the source is. -/
theorem primeReducedActiveRootPolynomial_ne_zero
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) :
    primeReducedActiveRootPolynomial p χ P ≠ 0 := by
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr hP0)
  · rw [Finset.prod_ne_zero_iff]
    intro a ha
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)

/-- The reduced active polynomial is visibly split. -/
theorem primeReducedActiveRootPolynomial_splits
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    (primeReducedActiveRootPolynomial p χ P).Splits := by
  apply Polynomial.Splits.mul (Polynomial.Splits.C _)
  apply Polynomial.Splits.prod
  intro a ha
  exact (Polynomial.Splits.X_sub_C a).pow _

/-- Its root multiset has the reduced active multiplicities. -/
theorem roots_primeReducedActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) :
    (primeReducedActiveRootPolynomial p χ P).roots =
      (primeActiveRoots p χ P).val.bind fun a =>
        (P.rootMultiplicity a % orderOf χ) •
          ({a} : Multiset (ZMod p)) := by
  let A := primeActiveRoots p χ P
  have hlc : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hprod :
      (∏ a ∈ A, (X - C a) ^
          (P.rootMultiplicity a % orderOf χ) :
        Polynomial (ZMod p)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)
  rw [primeReducedActiveRootPolynomial,
    Polynomial.roots_C_mul _ hlc,
    Polynomial.roots_prod _ A hprod]
  congr 1
  funext a
  rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C]

/-- Root multiplicities are precisely the nonzero least residues. -/
theorem rootMultiplicity_primeReducedActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) {a : ZMod p}
    (ha : a ∈ primeActiveRoots p χ P) :
    (primeReducedActiveRootPolynomial p χ P).rootMultiplicity a =
      P.rootMultiplicity a % orderOf χ := by
  rw [← Polynomial.count_roots,
    roots_primeReducedActiveRootPolynomial p χ P hP0,
    Multiset.count_bind]
  simp only [Multiset.count_nsmul, Multiset.count_singleton]
  change (∑ b ∈ primeActiveRoots p χ P,
      (P.rootMultiplicity b % orderOf χ) *
        if a = b then 1 else 0) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    rw [if_neg (Ne.symm hba), mul_zero]
  · exact fun h => (h ha).elim

/-- Reduction changes multiplicities but not the distinct active root set. -/
theorem roots_primeReducedActiveRootPolynomial_toFinset
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) :
    (primeReducedActiveRootPolynomial p χ P).roots.toFinset =
      primeActiveRoots p χ P := by
  classical
  rw [roots_primeReducedActiveRootPolynomial p χ P hP0]
  ext x
  simp only [Multiset.mem_toFinset, Multiset.mem_bind, Finset.mem_val,
    Multiset.mem_nsmul, Multiset.mem_singleton]
  constructor
  · rintro ⟨a, ha, hm, rfl⟩
    exact ha
  · intro hx
    exact ⟨x, hx,
      rootMultiplicity_mod_orderOf_ne_zero_of_mem_primeActiveRoots
        p χ P hx, rfl⟩

/-- Every root multiplicity lies in the canonical strict range below the
character order.  Positivity follows automatically from root membership. -/
def IsPrimeKummerReducedExponentPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : Prop :=
  ∀ a ∈ P.roots.toFinset, P.rootMultiplicity a < orderOf χ

/-- The canonical reduced active polynomial satisfies the strict exponent
range at every root. -/
theorem isPrimeKummerReducedExponentPolynomial_primeReducedActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) :
    IsPrimeKummerReducedExponentPolynomial χ
      (primeReducedActiveRootPolynomial p χ P) := by
  intro a ha
  have haSource : a ∈ primeActiveRoots p χ P := by
    rwa [roots_primeReducedActiveRootPolynomial_toFinset p χ P hP0] at ha
  rw [rootMultiplicity_primeReducedActiveRootPolynomial
    p χ P hP0 haSource]
  exact Nat.mod_lt _ (orderOf_pos χ)

/-- A polynomial whose positive root multiplicities are strictly below the
character order has no inactive roots. -/
theorem primeActiveRoots_eq_roots_of_reducedExponent
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hreduced : IsPrimeKummerReducedExponentPolynomial χ P) :
    primeActiveRoots p χ P = P.roots.toFinset := by
  apply Finset.filter_eq_self.mpr
  intro a ha
  rw [Polynomial.count_roots]
  have hpos : 0 < P.rootMultiplicity a := by
    rw [← Polynomial.count_roots P]
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp ha)
  exact Nat.not_dvd_of_pos_of_lt hpos (hreduced a ha)

/-- A nonempty reduced-exponent split polynomial is Kummer-nondegenerate. -/
theorem not_isMulCharOrderScalarPower_of_reducedExponent
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) (hP : P.Splits)
    (hreduced : IsPrimeKummerReducedExponentPolynomial χ P)
    (hroots : P.roots.toFinset.Nonempty) :
    ¬IsMulCharOrderScalarPower χ P := by
  rw [not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
    χ P hP0 hP]
  obtain ⟨a, ha⟩ := hroots
  refine ⟨a, ha, ?_⟩
  have hpos : 0 < P.rootMultiplicity a := by
    rw [← Polynomial.count_roots P]
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp ha)
  exact Nat.not_dvd_of_pos_of_lt hpos (hreduced a ha)

/-- Character evaluation of the reduced polynomial uses precisely the least
residue local characters. -/
theorem mulChar_eval_map_primeReducedActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (ψ : MulChar L ℂ) (x : L) :
    ψ (((primeReducedActiveRootPolynomial p χ P).map
        (algebraMap (ZMod p) L)).eval x) =
      ψ (algebraMap (ZMod p) L P.leadingCoeff) *
        ∏ a ∈ primeActiveRoots p χ P,
          (ψ ^ (P.rootMultiplicity a % orderOf χ))
            (x - algebraMap (ZMod p) L a) := by
  rw [eval_map_primeReducedActiveRootPolynomial, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  have hm : P.rootMultiplicity a % orderOf χ ≠ 0 :=
    rootMultiplicity_mod_orderOf_ne_zero_of_mem_primeActiveRoots
      p χ P ha
  rw [map_pow, MulChar.pow_apply' ψ hm]

/-- The base correlation is unchanged by exponent reduction. -/
theorem primePolynomialCharacterCorrelation_reducedActivePolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    primePolynomialCharacterCorrelation p χ
        (primeReducedActiveRootPolynomial p χ P) =
      primeActiveRootMainCorrelation p χ P := by
  unfold primePolynomialCharacterCorrelation
  rw [primeActiveRootMainCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [show χ ((primeReducedActiveRootPolynomial p χ P).eval x) =
      χ P.leadingCoeff *
        ∏ a ∈ primeActiveRoots p χ P,
          (χ ^ (P.rootMultiplicity a % orderOf χ)) (x - a) by
    simpa using
      (mulChar_eval_map_primeReducedActiveRootPolynomial p χ P χ x)]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [pow_mod_orderOf χ (P.rootMultiplicity a)]

/-- Norm lifting preserves the exponent-reduction identity. -/
theorem finiteFieldNormLift_pow_mod_orderOf
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (m : ℕ) : by
    let E := FiniteField.Extension (ZMod p) p d
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    exact χE ^ (m % orderOf χ) = χE ^ m := by
  let E := FiniteField.Extension (ZMod p) p d
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  have h := pow_mod_orderOf χE m
  rw [orderOf_finiteFieldNormLiftMulChar (ZMod p) E χ] at h
  exact h

/-- Every indexed Kummer trace is unchanged when active multiplicities are
replaced by their least positive residues. -/
theorem primeKummerExtensionCorrelation_reducedActivePolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    ∀ q : ℕ,
      primeKummerExtensionCorrelation p χ
          (primeReducedActiveRootPolynomial p χ P) q =
        primeKummerActiveCorrelation p χ P q
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primePolynomialCharacterCorrelation_reducedActivePolynomial]
      rfl
  | q + 1 => by
      rw [primeKummerExtensionCorrelation_succ_eq_normLift]
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      change (∑ x : E,
          χE (((primeReducedActiveRootPolynomial p χ P).map
            (algebraMap (ZMod p) E)).eval x)) =
        χE (algebraMap (ZMod p) E P.leadingCoeff) *
          ∑ x : E, ∏ a ∈ primeActiveRoots p χ P,
            (χE ^ P.rootMultiplicity a)
              (x - algebraMap (ZMod p) E a)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [mulChar_eval_map_primeReducedActiveRootPolynomial]
      congr 1
      apply Finset.prod_congr rfl
      intro a ha
      rw [finiteFieldNormLift_pow_mod_orderOf p d χ
        (P.rootMultiplicity a)]

/-- A full system for the reduced polynomial gives the active-root system of
the original source without changing its spectrum. -/
def PrimeKummerIsotypicFrobeniusSystem.toReducedActiveRootSystem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeReducedActiveRootPolynomial p χ P)) (hP0 : P ≠ 0) :
    PrimeKummerActiveFrobeniusSystem p χ P where
  rank := s.rank
  eigenvalue := s.eigenvalue
  rank_le := by
    simpa [roots_primeReducedActiveRootPolynomial_toFinset p χ P hP0] using
      s.rank_le
  integral := s.integral
  weight_le := s.weight_le
  trace_eq := fun q => by
    rw [← primeKummerExtensionCorrelation_reducedActivePolynomial p χ P q]
    exact s.extensionTrace_eq q

/-- The final geometric source with all local exponents in their canonical
finite range. -/
def TaoPrimeKummerReducedExponentFrobeniusSystemThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → IsPrimeKummerReducedExponentPolynomial χ P →
      3 ≤ P.roots.toFinset.card →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- The active-root source is equivalent to the reduced-exponent polynomial
source. -/
theorem taoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore_iff_reducedExponent :
    TaoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore ↔
      TaoPrimeKummerReducedExponentFrobeniusSystemThreeRootsOrMore := by
  constructor
  · intro hactive p _ _ χ P hχ hP hreduced hcard
    have hP0 : P ≠ 0 := by
      intro hzero
      subst P
      simp at hcard
    have hactiveEq :=
      primeActiveRoots_eq_roots_of_reducedExponent p χ P hreduced
    have hactiveCard : 3 ≤ (primeActiveRoots p χ P).card := by
      rw [hactiveEq]
      exact hcard
    have hpower := not_isMulCharOrderScalarPower_of_reducedExponent
      p χ P hP0 hP hreduced (Finset.card_pos.mp (by omega))
    exact (hactive p χ P hχ hP hpower hactiveCard).map
      (fun s => s.toFrobeniusSystem hP (by omega))
  · intro hreduced p _ _ χ P hχ hP hpower hcard
    have hP0 : P ≠ 0 := by
      intro hzero
      subst P
      exact hpower (isMulCharOrderScalarPower_zero χ)
    let Q := primeReducedActiveRootPolynomial p χ P
    have hQsplits : Q.Splits :=
      primeReducedActiveRootPolynomial_splits p χ P
    have hQreduced : IsPrimeKummerReducedExponentPolynomial χ Q :=
      isPrimeKummerReducedExponentPolynomial_primeReducedActiveRootPolynomial
        p χ P hP0
    have hQcard : 3 ≤ Q.roots.toFinset.card := by
      rw [roots_primeReducedActiveRootPolynomial_toFinset p χ P hP0]
      exact hcard
    exact (hreduced p χ Q hχ hQsplits hQreduced hQcard).map
      (fun s => s.toReducedActiveRootSystem hP0)

/-- The reduced finite-exponent cohomological source implies the complete
Kummer Frobenius theorem. -/
theorem TaoPrimeKummerReducedExponentFrobeniusSystemThreeRootsOrMore.toFull
    (hreduced :
      TaoPrimeKummerReducedExponentFrobeniusSystemThreeRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore.toFull
    (taoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore_iff_reducedExponent.mpr
      hreduced)

end

end Tao2026

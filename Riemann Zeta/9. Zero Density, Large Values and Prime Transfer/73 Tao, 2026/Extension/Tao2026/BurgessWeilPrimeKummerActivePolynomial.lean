import Tao2026.BurgessWeilPrimeKummerActiveFrobeniusSystem

/-!
# The canonical active Kummer polynomial

The unrestricted active-root trace is itself the ordinary Kummer trace of a
canonical split polynomial: retain the leading scalar and precisely the
active linear factors, with their original multiplicities.  This file makes
that reduction exact over the base field and every canonical extension.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The split polynomial obtained by deleting every inactive linear factor. -/
def primeActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    Polynomial (ZMod p) :=
  C P.leadingCoeff *
    ∏ a ∈ primeActiveRoots p χ P,
      (X - C a) ^ P.rootMultiplicity a

/-- Evaluation of the active polynomial after arbitrary scalar extension. -/
theorem eval_map_primeActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    {L : Type*} [Field L] [Algebra (ZMod p) L] (x : L) :
    ((primeActiveRootPolynomial p χ P).map
        (algebraMap (ZMod p) L)).eval x =
      algebraMap (ZMod p) L P.leadingCoeff *
        ∏ a ∈ primeActiveRoots p χ P,
          (x - algebraMap (ZMod p) L a) ^ P.rootMultiplicity a := by
  rw [Polynomial.eval_map]
  change (Polynomial.eval₂RingHom (algebraMap (ZMod p) L) x)
      (C P.leadingCoeff *
        ∏ a ∈ primeActiveRoots p χ P,
          (X - C a) ^ P.rootMultiplicity a) = _
  rw [map_mul]
  have hC :
      (Polynomial.eval₂RingHom (algebraMap (ZMod p) L) x)
          (C P.leadingCoeff) =
        algebraMap (ZMod p) L P.leadingCoeff := by
    change Polynomial.eval₂ (algebraMap (ZMod p) L) x
      (C P.leadingCoeff) = _
    exact Polynomial.eval₂_C _ _
  rw [hC]
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  simp

/-- The active polynomial is nonzero whenever the source polynomial is. -/
theorem primeActiveRootPolynomial_ne_zero
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) :
    primeActiveRootPolynomial p χ P ≠ 0 := by
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr hP0)
  · rw [Finset.prod_ne_zero_iff]
    intro a ha
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)

/-- The active polynomial is visibly split. -/
theorem primeActiveRootPolynomial_splits
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    (primeActiveRootPolynomial p χ P).Splits := by
  apply Polynomial.Splits.mul (Polynomial.Splits.C _)
  apply Polynomial.Splits.prod
  intro a ha
  exact (Polynomial.Splits.X_sub_C a).pow _

/-- The root multiset of the active polynomial retains the source
multiplicity at every active root. -/
theorem roots_primeActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) :
    (primeActiveRootPolynomial p χ P).roots =
      (primeActiveRoots p χ P).val.bind fun a =>
        P.rootMultiplicity a • ({a} : Multiset (ZMod p)) := by
  let A := primeActiveRoots p χ P
  have hlc : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hprod :
      (∏ a ∈ A, (X - C a) ^ P.rootMultiplicity a :
        Polynomial (ZMod p)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)
  rw [primeActiveRootPolynomial, Polynomial.roots_C_mul _ hlc,
    Polynomial.roots_prod _ A hprod]
  congr 1
  funext a
  rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C]

/-- Multiplicity is unchanged at every retained active root. -/
theorem rootMultiplicity_primeActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) {a : ZMod p}
    (ha : a ∈ primeActiveRoots p χ P) :
    (primeActiveRootPolynomial p χ P).rootMultiplicity a =
      P.rootMultiplicity a := by
  rw [← Polynomial.count_roots,
    roots_primeActiveRootPolynomial p χ P hP0,
    Multiset.count_bind]
  simp only [Multiset.count_nsmul, Multiset.count_singleton]
  change (∑ b ∈ primeActiveRoots p χ P,
      P.rootMultiplicity b * if a = b then 1 else 0) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    rw [if_neg (Ne.symm hba), mul_zero]
  · exact fun h => (h ha).elim

/-- The distinct roots of the active polynomial are exactly the active roots
of the source polynomial. -/
theorem roots_primeActiveRootPolynomial_toFinset
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) :
    (primeActiveRootPolynomial p χ P).roots.toFinset =
      primeActiveRoots p χ P := by
  classical
  let A := primeActiveRoots p χ P
  have hlc : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hprod :
      (∏ a ∈ A, (X - C a) ^ P.rootMultiplicity a :
        Polynomial (ZMod p)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)
  rw [primeActiveRootPolynomial, Polynomial.roots_C_mul _ hlc,
    Polynomial.roots_prod _ A hprod]
  ext x
  simp only [Multiset.mem_toFinset, Multiset.mem_bind, Finset.mem_val,
    Polynomial.roots_pow, Multiset.mem_nsmul,
    Polynomial.roots_X_sub_C, Multiset.mem_singleton]
  constructor
  · rintro ⟨a, ha, hm, rfl⟩
    exact ha
  · intro hx
    refine ⟨x, hx, ?_, rfl⟩
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr
      (Multiset.mem_toFinset.mp
        (primeActiveRoots_subset_roots p χ P hx))).ne'

/-- Every root retained in the active polynomial remains active, so there are
no inactive roots left. -/
theorem primeActiveRoots_primeActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) :
    primeActiveRoots p χ (primeActiveRootPolynomial p χ P) =
      (primeActiveRootPolynomial p χ P).roots.toFinset := by
  apply Finset.filter_eq_self.mpr
  intro a ha
  have haSource : a ∈ primeActiveRoots p χ P := by
    rwa [roots_primeActiveRootPolynomial_toFinset p χ P hP0] at ha
  have hnot : ¬orderOf χ ∣ P.rootMultiplicity a := by
    have := (Finset.mem_filter.mp haSource).2
    rwa [Polynomial.count_roots] at this
  rw [Polynomial.count_roots,
    rootMultiplicity_primeActiveRootPolynomial p χ P hP0 haSource]
  exact hnot

/-- If at least one active root is retained, the active polynomial is not a
character-order scalar power. -/
theorem not_isMulCharOrderScalarPower_primeActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) (hactive : (primeActiveRoots p χ P).Nonempty) :
    ¬IsMulCharOrderScalarPower χ (primeActiveRootPolynomial p χ P) := by
  rw [not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
    χ (primeActiveRootPolynomial p χ P)
    (primeActiveRootPolynomial_ne_zero p χ P hP0)
    (primeActiveRootPolynomial_splits p χ P)]
  obtain ⟨a, ha⟩ := hactive
  refine ⟨a, ?_, ?_⟩
  · rwa [roots_primeActiveRootPolynomial_toFinset p χ P hP0]
  · rw [rootMultiplicity_primeActiveRootPolynomial p χ P hP0 ha]
    have hnot := (Finset.mem_filter.mp ha).2
    rwa [Polynomial.count_roots] at hnot

/-- Applying any multiplicative character after scalar extension gives the
local-character product defining the active trace. -/
theorem mulChar_eval_map_primeActiveRootPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (ψ : MulChar L ℂ) (x : L) :
    ψ (((primeActiveRootPolynomial p χ P).map
        (algebraMap (ZMod p) L)).eval x) =
      ψ (algebraMap (ZMod p) L P.leadingCoeff) *
        ∏ a ∈ primeActiveRoots p χ P,
          (ψ ^ P.rootMultiplicity a)
            (x - algebraMap (ZMod p) L a) := by
  rw [eval_map_primeActiveRootPolynomial, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  have hm : P.rootMultiplicity a ≠ 0 := by
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr
      (Multiset.mem_toFinset.mp
        (primeActiveRoots_subset_roots p χ P ha))).ne'
  rw [map_pow, MulChar.pow_apply' ψ hm]

/-- The base-field correlation of the active polynomial is the unrestricted
active-root main correlation. -/
theorem primePolynomialCharacterCorrelation_activePolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    primePolynomialCharacterCorrelation p χ
        (primeActiveRootPolynomial p χ P) =
      primeActiveRootMainCorrelation p χ P := by
  unfold primePolynomialCharacterCorrelation
  rw [primeActiveRootMainCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simpa using
    (mulChar_eval_map_primeActiveRootPolynomial p χ P χ x)

/-- In every indexed degree, the ordinary Kummer trace of the active
polynomial is exactly the active trace of the source polynomial. -/
theorem primeKummerExtensionCorrelation_activePolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    ∀ q : ℕ,
      primeKummerExtensionCorrelation p χ
          (primeActiveRootPolynomial p χ P) q =
        primeKummerActiveCorrelation p χ P q
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primePolynomialCharacterCorrelation_activePolynomial]
      rfl
  | q + 1 => by
      rw [primeKummerExtensionCorrelation_succ_eq_normLift]
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      change (∑ x : E,
          χE (((primeActiveRootPolynomial p χ P).map
            (algebraMap (ZMod p) E)).eval x)) =
        χE (algebraMap (ZMod p) E P.leadingCoeff) *
          ∑ x : E, ∏ a ∈ primeActiveRoots p χ P,
            (χE ^ P.rootMultiplicity a)
              (x - algebraMap (ZMod p) E a)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      exact mulChar_eval_map_primeActiveRootPolynomial p χ P χE x

/-- A full Frobenius system for the canonical active polynomial is exactly an
active-root Frobenius system for the source polynomial. -/
def PrimeKummerIsotypicFrobeniusSystem.toActiveRootSystem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeActiveRootPolynomial p χ P)) (hP0 : P ≠ 0) :
    PrimeKummerActiveFrobeniusSystem p χ P where
  rank := s.rank
  eigenvalue := s.eigenvalue
  rank_le := by
    simpa [roots_primeActiveRootPolynomial_toFinset p χ P hP0] using
      s.rank_le
  integral := s.integral
  weight_le := s.weight_le
  trace_eq := fun q => by
    rw [← primeKummerExtensionCorrelation_activePolynomial p χ P q]
    exact s.extensionTrace_eq q

/-- The genuinely geometric source restricted to split polynomials for which
every distinct root is active. -/
def TaoPrimeKummerAllActiveFrobeniusSystemThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      primeActiveRoots p χ P = P.roots.toFinset →
        3 ≤ P.roots.toFinset.card →
          Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- The active-trace source is equivalent to ordinary Kummer cohomology on
the strictly all-active polynomial family. -/
theorem taoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore_iff_allActive :
    TaoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore ↔
      TaoPrimeKummerAllActiveFrobeniusSystemThreeRootsOrMore := by
  constructor
  · intro hactive p _ _ χ P hχ hP hpower hactiveEq hcard
    have hcardActive : 3 ≤ (primeActiveRoots p χ P).card := by
      rw [hactiveEq]
      exact hcard
    exact (hactive p χ P hχ hP hpower hcardActive).map
      (fun s => s.toFrobeniusSystem hP (by omega))
  · intro hall p _ _ χ P hχ hP hpower hcard
    have hP0 : P ≠ 0 := by
      intro hzero
      subst P
      exact hpower (isMulCharOrderScalarPower_zero χ)
    let Q := primeActiveRootPolynomial p χ P
    have hQ0 : Q ≠ 0 :=
      primeActiveRootPolynomial_ne_zero p χ P hP0
    have hQsplits : Q.Splits :=
      primeActiveRootPolynomial_splits p χ P
    have hQroots : Q.roots.toFinset = primeActiveRoots p χ P :=
      roots_primeActiveRootPolynomial_toFinset p χ P hP0
    have hQactive : primeActiveRoots p χ Q = Q.roots.toFinset :=
      primeActiveRoots_primeActiveRootPolynomial p χ P hP0
    have hQpower : ¬IsMulCharOrderScalarPower χ Q :=
      not_isMulCharOrderScalarPower_primeActiveRootPolynomial p χ P hP0
        (Finset.card_pos.mp (by omega))
    have hQcard : 3 ≤ Q.roots.toFinset.card := by
      rw [hQroots]
      exact hcard
    exact (hall p χ Q hχ hQsplits hQpower hQactive hQcard).map
      (fun s => s.toActiveRootSystem hP0)

/-- Consequently the all-active geometric source alone implies the complete
Kummer Frobenius theorem and hence the fixed-`r=7` Burgess input. -/
theorem TaoPrimeKummerAllActiveFrobeniusSystemThreeRootsOrMore.toFull
    (hall : TaoPrimeKummerAllActiveFrobeniusSystemThreeRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore.toFull
    (taoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore_iff_allActive.mpr
      hall)

end

end Tao2026

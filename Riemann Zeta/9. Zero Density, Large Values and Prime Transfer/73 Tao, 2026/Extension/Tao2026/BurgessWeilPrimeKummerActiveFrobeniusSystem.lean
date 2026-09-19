import Tao2026.BurgessWeilPrimeKummerLowActiveFrobenius

/-!
# The active-root Kummer Frobenius system

The remaining cohomological object is the unrestricted character sum over the
active roots.  Inactive roots are already explicit weight-zero eigenvalues.
This file packages the active trace sequence and proves that any bounded-rank
active Frobenius system extends canonically to the full polynomial system.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def primeActiveRootMainCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : ℂ :=
  χ P.leadingCoeff *
    ∑ x : ZMod p, ∏ a ∈ primeActiveRoots p χ P,
      (χ ^ P.rootMultiplicity a) (x - a)

theorem primeActiveRootMainCorrelation_eq_countForm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    primeActiveRootMainCorrelation p χ P =
      χ P.leadingCoeff *
        (∑ x : ZMod p, ∏ a ∈ primeActiveRoots p χ P,
          χ (x - a) ^ P.roots.count a) := by
  unfold primeActiveRootMainCorrelation
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro a ha
  have haRoot := primeActiveRoots_subset_roots p χ P ha
  have hcount : P.roots.count a ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haRoot)).ne'
  rw [← Polynomial.count_roots P, MulChar.pow_apply' χ hcount]

/-- The active-root trace sequence, indexed exactly like
`primeKummerExtensionCorrelation`: index zero is the base field and successor
`q+1` uses extension degree `q+2`. -/
def primeKummerActiveCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : ℕ → ℂ
  | 0 => primeActiveRootMainCorrelation p χ P
  | q + 1 => by
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      exact primeHigherActiveRootCharacterSum p d χ P

/-- Uniformly in every extension index, the full trace is the active trace
minus the power sum of all inactive-root deleted values. -/
theorem primeKummerExtensionCorrelation_eq_active_sub_inactivePowers
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) :
    ∀ q : ℕ, primeKummerExtensionCorrelation p χ P q =
      primeKummerActiveCorrelation p χ P q -
        ∑ c ∈ primeInactiveRoots p χ P,
          primeActiveDeletedTerm p χ P c ^ (q + 1)
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primePolynomialCharacterCorrelation_eq_activeSum_sub_inactive
          p χ P hP,
        ← primeActiveRootMainCorrelation_eq_countForm]
      simp [primeKummerActiveCorrelation]
  | q + 1 => by
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      rw [primeKummerExtensionCorrelation_succ_eq_activeSum_sub_inactive
        p χ P hP q]
      change primeHigherActiveRootCharacterSum p d χ P -
          (∑ c ∈ primeInactiveRoots p χ P,
            primeHigherActiveDeletedTerm p d χ P c) =
        primeHigherActiveRootCharacterSum p d χ P - _
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      rw [primeHigherActiveDeletedTerm_eq_pow]

/-- Frobenius data for the unrestricted active-root trace.  Its natural
conductor bound is the number of active roots minus one. -/
structure PrimeKummerActiveFrobeniusSystem
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) where
  rank : ℕ
  eigenvalue : Fin rank → ℂ
  rank_le : rank ≤ (primeActiveRoots p χ P).card - 1
  integral : ∀ i, IsIntegral ℤ (eigenvalue i)
  weight_le : ∀ i, ‖eigenvalue i‖ ≤ Real.sqrt p
  trace_eq : ∀ q : ℕ,
    primeKummerActiveCorrelation p χ P q =
      -∑ i : Fin rank, eigenvalue i ^ (q + 1)

/-- Append all inactive-root deleted values to an active Frobenius spectrum. -/
def PrimeKummerActiveFrobeniusSystem.fullEigenvalue
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerActiveFrobeniusSystem p χ P) :
    Fin (s.rank + (primeInactiveRoots p χ P).card) → ℂ :=
  Fin.addCases s.eigenvalue (primeSingleActiveEigenvalue p χ P)

@[simp]
theorem PrimeKummerActiveFrobeniusSystem.sum_fullEigenvalue_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerActiveFrobeniusSystem p χ P) (d : ℕ) :
    (∑ i, s.fullEigenvalue i ^ d) =
      (∑ i : Fin s.rank, s.eigenvalue i ^ d) +
        ∑ c ∈ primeInactiveRoots p χ P,
          primeActiveDeletedTerm p χ P c ^ d := by
  rw [Fin.sum_univ_add]
  simp only [PrimeKummerActiveFrobeniusSystem.fullEigenvalue,
    Fin.addCases_left, Fin.addCases_right,
    sum_primeSingleActiveEigenvalue_pow]

/-- The active system plus explicit inactive eigenvalues gives the full
polynomial Frobenius system without losing the conductor bound. -/
def PrimeKummerActiveFrobeniusSystem.toFrobeniusSystem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerActiveFrobeniusSystem p χ P)
    (hP : P.Splits) (hactive : 0 < (primeActiveRoots p χ P).card) :
    PrimeKummerIsotypicFrobeniusSystem p χ P := by
  have hcard := card_primeActiveRoots_add_card_primeInactiveRoots p χ P
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  refine {
    rank := s.rank + (primeInactiveRoots p χ P).card
    eigenvalue := s.fullEigenvalue
    rank_le := by
      calc
        s.rank + (primeInactiveRoots p χ P).card ≤
            ((primeActiveRoots p χ P).card - 1) +
              (primeInactiveRoots p χ P).card :=
          Nat.add_le_add_right s.rank_le _
        _ = P.roots.toFinset.card - 1 := by omega
    integral := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa [PrimeKummerActiveFrobeniusSystem.fullEigenvalue] using s.integral j
      · simpa [PrimeKummerActiveFrobeniusSystem.fullEigenvalue] using
          isIntegral_primeActiveDeletedTerm p χ P
            (finEquivFinset (primeInactiveRoots p χ P) j)
    weight_le := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa [PrimeKummerActiveFrobeniusSystem.fullEigenvalue] using s.weight_le j
      · simpa [PrimeKummerActiveFrobeniusSystem.fullEigenvalue] using
          (norm_primeActiveDeletedTerm_le_one p χ P
            (finEquivFinset (primeInactiveRoots p χ P) j)).trans hsqrt
    trace_eq := by
      have hcorr := primeKummerExtensionCorrelation_eq_active_sub_inactivePowers
        p χ P hP 0
      rw [primeKummerExtensionCorrelation_zero] at hcorr
      have hsum := s.sum_fullEigenvalue_pow 1
      simp only [pow_one] at hsum
      rw [hsum]
      have htrace := s.trace_eq 0
      simp at htrace hcorr
      rw [htrace] at hcorr
      linear_combination hcorr
    extensionTrace_eq := fun q => by
      rw [s.sum_fullEigenvalue_pow]
      rw [primeKummerExtensionCorrelation_eq_active_sub_inactivePowers
        p χ P hP q, s.trace_eq q]
      ring }

/-- The remaining active-root cohomological source proposition. -/
def TaoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      3 ≤ (primeActiveRoots p χ P).card →
        Nonempty (PrimeKummerActiveFrobeniusSystem p χ P)

/-- The active-root cohomological source implies the complete Kummer
Frobenius theorem. -/
theorem TaoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore.toFull
    (hactiveSystem : TaoPrimeKummerActiveFrobeniusSystemThreeActiveRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSystem := by
  apply TaoPrimeKummerIsotypicFrobeniusSystemThreeActiveRootsOrMore.toFull
  intro p _ _ χ P hχ hP hpower hactive
  exact (hactiveSystem p χ P hχ hP hpower hactive).map
    (fun s => s.toFrobeniusSystem hP (by omega))

end

end Tao2026

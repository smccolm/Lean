import Tao2026.BurgessWeilPrimeKummerRootMultisetSpectrum
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Canonical higher-root Frobenius spectra

Newton's identities show that a finite complex multiset is determined by its
cardinality and all of its positive power sums.  The literal extension traces
in `PrimeKummerExplicitRootMultisetSpectrum` supply exactly those power sums.
Consequently, whenever the higher-root spectrum exists, it is unique as a
multiset (including multiplicities), and so is its Frobenius polynomial.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators

noncomputable section

private theorem complexFin_newtonIdentity
    {n : ℕ} (f : Fin n → ℂ) (k : ℕ) :
    (k : ℂ) * ((Finset.univ.val.map f).esymm k) =
      (-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1 : ℂ) ^ a.1 * (Finset.univ.val.map f).esymm a.1 *
            ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f)
    (MvPolynomial.mul_esymm_eq_sum (Fin n) ℤ k)
  have hesymm (j : ℕ) :
      MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℤ j) =
        (Finset.univ.val.map f).esymm j :=
    MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ j f
  simp_rw [map_mul, map_pow, map_neg, map_one] at h
  simp [MvPolynomial.psum] at h
  have hsum :
      (∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1 : ℂ) ^ a.1 *
            MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℤ a.1) *
              ∑ i, f i ^ a.2) =
        ∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1 : ℂ) ^ a.1 * (Finset.univ.val.map f).esymm a.1 *
            ∑ i, f i ^ a.2 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hesymm]
  rw [hsum, hesymm k] at h
  exact h

/-- Newton's identity evaluated on an arbitrary finite multiset of complex
numbers.  This formulation retains repeated roots. -/
theorem complexMultiset_newtonIdentity (A : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * A.esymm k =
      (-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1 : ℂ) ^ a.1 * A.esymm a.1 *
            (A.map fun z => z ^ a.2).sum := by
  let l := primeKummerSpectralList A
  have h := complexFin_newtonIdentity l.get k
  have henum : Finset.univ.val.map l.get = A := by
    rw [Fin.univ_val_map, List.ofFn_get]
    exact coe_primeKummerSpectralList A
  have hp (j : ℕ) :
      (∑ i : Fin l.length, l.get i ^ j) =
        (A.map fun z => z ^ j).sum := by
    calc
      _ = (List.ofFn (fun i : Fin l.length => l.get i ^ j)).sum :=
        List.sum_ofFn.symm
      _ = (List.map (fun z => z ^ j) l).sum := by
        congr 1
        apply List.ext_get
        · simp
        · intro n hn₁ hn₂
          simp
      _ = (A.map fun z => z ^ j).sum := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe,
          coe_primeKummerSpectralList]
  rw [henum] at h
  simp_rw [hp] at h
  exact h

/-- Positive power sums determine every elementary symmetric sum over
`ℂ`. -/
theorem complexMultiset_esymm_eq_of_powerSums_eq (A B : Multiset ℂ)
    (hp : ∀ k : ℕ, 0 < k →
      (A.map fun z => z ^ k).sum = (B.map fun z => z ^ k).sum) :
    ∀ k : ℕ, A.esymm k = B.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k = 0
      · subst k
        simp [Multiset.esymm]
      · have hA := complexMultiset_newtonIdentity A k
        have hB := complexMultiset_newtonIdentity B k
        have hsum :
            (∑ a ∈ Finset.antidiagonal k with a.1 < k,
              (-1 : ℂ) ^ a.1 * A.esymm a.1 *
                (A.map fun z => z ^ a.2).sum) =
              ∑ a ∈ Finset.antidiagonal k with a.1 < k,
                (-1 : ℂ) ^ a.1 * B.esymm a.1 *
                  (B.map fun z => z ^ a.2).sum := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha' := ha
          simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha'
          have ha2pos : 0 < a.2 := by omega
          rw [ih a.1 ha'.2, hp a.2 ha2pos]
        have hmul : (k : ℂ) * A.esymm k = (k : ℂ) * B.esymm k := by
          rw [hA, hB, hsum]
        exact mul_left_cancel₀ (by exact_mod_cast hk) hmul

/-- A finite complex multiset is determined, with multiplicity, by its
cardinality and all positive power sums. -/
theorem complexMultiset_eq_of_card_eq_of_powerSums_eq (A B : Multiset ℂ)
    (hcard : A.card = B.card)
    (hp : ∀ k : ℕ, 0 < k →
      (A.map fun z => z ^ k).sum = (B.map fun z => z ^ k).sum) :
    A = B := by
  have hesymm := complexMultiset_esymm_eq_of_powerSums_eq A B hp
  have hpoly :
      (A.map fun z => Polynomial.X - Polynomial.C z).prod =
        (B.map fun z => Polynomial.X - Polynomial.C z).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,
      Multiset.prod_X_sub_X_eq_sum_esymm, hcard]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hesymm]
  calc
    A = ((A.map fun z => Polynomial.X - Polynomial.C z).prod).roots :=
      (Polynomial.roots_multiset_prod_X_sub_C A).symm
    _ = ((B.map fun z => Polynomial.X - Polynomial.C z).prod).roots := by
      rw [hpoly]
    _ = B := Polynomial.roots_multiset_prod_X_sub_C B

/-- The literal extension traces and prescribed cardinality make a Kummer
root multiset spectrum unique. -/
theorem primeKummerExplicitRootMultisetSpectrum_unique
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s t : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    s = t := by
  have heig : s.eigenvalues = t.eigenvalues := by
    apply complexMultiset_eq_of_card_eq_of_powerSums_eq
    · rw [s.card_eq, t.card_eq]
    · intro k hk
      have hs := s.trace_eq (k - 1)
      have ht := t.trace_eq (k - 1)
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
      rw [hk'] at hs ht
      apply neg_injective
      exact hs.symm.trans ht
  cases s
  cases t
  cases heig
  rfl

instance primeKummerExplicitRootMultisetSpectrum_subsingleton
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    Subsingleton (PrimeKummerExplicitRootMultisetSpectrum p χ R) :=
  ⟨primeKummerExplicitRootMultisetSpectrum_unique⟩

/-- A witness to the higher-root spectrum, when supplied, has a canonical
value because the spectrum type is a subsingleton. -/
def primeKummerCanonicalRootMultisetSpectrum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (h : Nonempty (PrimeKummerExplicitRootMultisetSpectrum p χ R)) :
    PrimeKummerExplicitRootMultisetSpectrum p χ R :=
  Classical.choice h

theorem primeKummerCanonicalRootMultisetSpectrum_eq
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (h : Nonempty (PrimeKummerExplicitRootMultisetSpectrum p χ R))
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    primeKummerCanonicalRootMultisetSpectrum h = s :=
  Subsingleton.elim _ _

/-- The higher-root source stated as unique existence rather than arbitrary
existence.  The proposition `True` is intentional: all admissibility data are
already fields of the spectrum record. -/
def TaoPrimeKummerUniqueRootMultisetSpectrumFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        ∃! _s : PrimeKummerExplicitRootMultisetSpectrum p χ R, True

theorem taoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore_iff_unique :
    TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore ↔
      TaoPrimeKummerUniqueRootMultisetSpectrumFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    obtain ⟨s⟩ := h p χ R hχ hzero hone hcard hreduced
    exact ⟨s, trivial, fun t _ => Subsingleton.elim t s⟩
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    obtain ⟨s, _hs, _hunique⟩ :=
      h p χ R hχ hzero hone hcard hreduced
    exact ⟨s⟩

end
end Tao2026

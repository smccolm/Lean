import Tao2026.BurgessWeilPrimeKummerCanonicalRootMultisetSpectrum

/-!
# Newton reconstruction of the higher-root Frobenius polynomial

The first `#support - 1` literal extension correlations determine the
elementary symmetric coefficients of the higher-root spectrum by Newton's
identities.  This file constructs that polynomial without assuming a
spectrum, proves it is monic of the expected degree, and takes its roots as
an unconditional canonical eigenvalue multiset.

Existence of the earlier spectral record is then equivalent to concrete
integrality, weight, and all-extension trace properties of these fixed roots.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators

noncomputable section

/-- Elementary symmetric coefficients reconstructed recursively from an
arbitrary complex power-sum sequence. -/
def complexNewtonElementary (powerSum : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 =>
      (k + 1 : ℂ)⁻¹ * ((-1 : ℂ) ^ (k + 2) *
        ∑ a ∈ ({a ∈ Finset.antidiagonal (k + 1) | a.1 < k + 1}).attach,
          (-1 : ℂ) ^ (a : ℕ × ℕ).1 *
            complexNewtonElementary powerSum (a : ℕ × ℕ).1 *
              powerSum (a : ℕ × ℕ).2)
termination_by k => k
decreasing_by
  have ha := a.property
  simp only [Finset.mem_filter] at ha
  omega

theorem complexNewtonElementary_succ (powerSum : ℕ → ℂ) (k : ℕ) :
    complexNewtonElementary powerSum (k + 1) =
      (k + 1 : ℂ)⁻¹ * ((-1 : ℂ) ^ (k + 2) *
        ∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
          (-1 : ℂ) ^ a.1 * complexNewtonElementary powerSum a.1 * powerSum a.2) := by
  rw [complexNewtonElementary]
  congr 2
  let S := {a ∈ Finset.antidiagonal (k + 1) | a.1 < k + 1}
  simpa [S] using
    (Finset.sum_attach S (fun a : ℕ × ℕ =>
      (-1 : ℂ) ^ a.1 * complexNewtonElementary powerSum a.1 * powerSum a.2))

/-- Applied to the power sums of a multiset, the recursive coefficients are
its elementary symmetric sums. -/
theorem complexNewtonElementary_powerSum_eq_esymm (A : Multiset ℂ) :
    ∀ k : ℕ,
      complexNewtonElementary (fun d => (A.map fun z => z ^ d).sum) k =
        A.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => simp [complexNewtonElementary, Multiset.esymm]
      | succ k =>
          rw [complexNewtonElementary_succ]
          have hsum :
              (∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                (-1 : ℂ) ^ a.1 *
                  complexNewtonElementary
                    (fun d => (A.map fun z => z ^ d).sum) a.1 *
                  (A.map fun z => z ^ a.2).sum) =
                ∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                  (-1 : ℂ) ^ a.1 * A.esymm a.1 *
                    (A.map fun z => z ^ a.2).sum := by
            apply Finset.sum_congr rfl
            intro a ha
            have ha' := ha
            simp only [Finset.mem_filter] at ha'
            rw [ih a.1 ha'.2]
          rw [hsum]
          have hnewton := complexMultiset_newtonIdentity A (k + 1)
          have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
          rw [← hnewton]
          field_simp
          simp

def primeRootMultisetSpectralRank {p : ℕ} (R : Multiset (ZMod p)) : ℕ :=
  R.toFinset.card - 1

/-- The candidate power sums read directly from the literal extension
correlations.  Degree zero is the prescribed spectral rank. -/
def primeRootMultisetNewtonPowerSum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : ℕ → ℂ
  | 0 => primeRootMultisetSpectralRank R
  | d + 1 => -primeRootMultisetExtensionCorrelation p χ R d

theorem PrimeKummerExplicitRootMultisetSpectrum.newtonPowerSum_eq
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    ∀ d : ℕ, primeRootMultisetNewtonPowerSum p χ R d =
      (s.eigenvalues.map fun z => z ^ d).sum := by
  intro d
  cases d with
  | zero =>
      simp [primeRootMultisetNewtonPowerSum, primeRootMultisetSpectralRank,
        s.card_eq]
  | succ d =>
      rw [primeRootMultisetNewtonPowerSum, s.trace_eq]
      simp

def primeRootMultisetNewtonElementary
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (j : ℕ) : ℂ :=
  complexNewtonElementary (primeRootMultisetNewtonPowerSum p χ R) j

theorem PrimeKummerExplicitRootMultisetSpectrum.newtonElementary_eq_esymm
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) (j : ℕ) :
    primeRootMultisetNewtonElementary p χ R j = s.eigenvalues.esymm j := by
  unfold primeRootMultisetNewtonElementary
  rw [← complexNewtonElementary_powerSum_eq_esymm s.eigenvalues j]
  congr 2
  funext d
  exact s.newtonPowerSum_eq d

/-- The characteristic polynomial reconstructed from the literal trace
sequence by Newton's identities. -/
def primeRootMultisetNewtonPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (primeRootMultisetSpectralRank R + 1),
    (-1 : Polynomial ℂ) ^ j *
      (Polynomial.C (primeRootMultisetNewtonElementary p χ R j) *
        Polynomial.X ^ (primeRootMultisetSpectralRank R - j))

theorem PrimeKummerExplicitRootMultisetSpectrum.newtonPolynomial_eq
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    primeRootMultisetNewtonPolynomial p χ R = s.frobeniusPolynomial := by
  rw [primeRootMultisetNewtonPolynomial,
    PrimeKummerExplicitRootMultisetSpectrum.frobeniusPolynomial,
    Multiset.prod_X_sub_X_eq_sum_esymm]
  rw [s.card_eq]
  apply Finset.sum_congr rfl
  intro j hj
  rw [s.newtonElementary_eq_esymm]
  simp [primeRootMultisetSpectralRank]

theorem primeRootMultisetNewtonPolynomial_isMonicOfDegree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    (primeRootMultisetNewtonPolynomial p χ R).IsMonicOfDegree
      (primeRootMultisetSpectralRank R) := by
  let n := primeRootMultisetSpectralRank R
  have hterm (j : ℕ) :
      ((-1 : Polynomial ℂ) ^ j *
        (Polynomial.C (primeRootMultisetNewtonElementary p χ R j) *
          Polynomial.X ^ (primeRootMultisetSpectralRank R - j))).natDegree ≤
        n - j := by
    calc
      _ ≤ ((-1 : Polynomial ℂ) ^ j).natDegree +
          (Polynomial.C (primeRootMultisetNewtonElementary p χ R j) *
            Polynomial.X ^ (primeRootMultisetSpectralRank R - j)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + (0 + (primeRootMultisetSpectralRank R - j)) := by
        apply Nat.add_le_add
        · simp
        · exact Polynomial.natDegree_mul_le.trans (by simp)
      _ = n - j := by simp [n]
  apply (Polynomial.isMonicOfDegree_iff _ _).mpr
  constructor
  · unfold primeRootMultisetNewtonPolynomial
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (hterm j).trans (Nat.sub_le _ _)
  · unfold primeRootMultisetNewtonPolynomial
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single 0]
    · simp [primeRootMultisetNewtonElementary, complexNewtonElementary]
    · intro j hj hj0
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hjle : j ≤ n := by
        simpa [n, Nat.lt_succ_iff] using hj
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      exact (hterm j).trans_lt (by omega)
    · simp

theorem primeRootMultisetNewtonPolynomial_monic
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    (primeRootMultisetNewtonPolynomial p χ R).Monic :=
  (primeRootMultisetNewtonPolynomial_isMonicOfDegree p χ R).monic

theorem primeRootMultisetNewtonPolynomial_natDegree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    (primeRootMultisetNewtonPolynomial p χ R).natDegree =
      primeRootMultisetSpectralRank R :=
  (primeRootMultisetNewtonPolynomial_isMonicOfDegree p χ R).natDegree_eq

/-- The fixed multiset of roots of the Newton-reconstructed polynomial. -/
def primeRootMultisetCanonicalEigenvalues
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Multiset ℂ :=
  (primeRootMultisetNewtonPolynomial p χ R).roots

theorem card_primeRootMultisetCanonicalEigenvalues
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    (primeRootMultisetCanonicalEigenvalues p χ R).card =
      primeRootMultisetSpectralRank R := by
  unfold primeRootMultisetCanonicalEigenvalues
  rw [← (IsAlgClosed.splits
    (primeRootMultisetNewtonPolynomial p χ R)).natDegree_eq_card_roots,
    primeRootMultisetNewtonPolynomial_natDegree]

theorem PrimeKummerExplicitRootMultisetSpectrum.canonicalEigenvalues_eq
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    primeRootMultisetCanonicalEigenvalues p χ R = s.eigenvalues := by
  unfold primeRootMultisetCanonicalEigenvalues
  rw [s.newtonPolynomial_eq, s.frobeniusPolynomial_roots]

/-- The higher-root spectral conditions expressed solely using the fixed
Newton polynomial and its canonical roots. -/
def PrimeRootMultisetNewtonSpectrumConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
      IsIntegral ℤ a) ∧
  (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
      ‖a‖ ≤ Real.sqrt p) ∧
  ∀ q : ℕ,
    primeRootMultisetExtensionCorrelation p χ R q =
      -((primeRootMultisetCanonicalEigenvalues p χ R).map
        fun a => a ^ (q + 1)).sum

theorem nonempty_primeKummerExplicitRootMultisetSpectrum_iff_newtonConditions
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    Nonempty (PrimeKummerExplicitRootMultisetSpectrum p χ R) ↔
      PrimeRootMultisetNewtonSpectrumConditions p χ R := by
  constructor
  · rintro ⟨s⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [s.canonicalEigenvalues_eq] at ha
      exact s.integral a ha
    · intro a ha
      rw [s.canonicalEigenvalues_eq] at ha
      exact s.weight_le a ha
    · intro q
      rw [s.canonicalEigenvalues_eq]
      exact s.trace_eq q
  · rintro ⟨hintegral, hweight, htrace⟩
    refine ⟨{
      eigenvalues := primeRootMultisetCanonicalEigenvalues p χ R
      card_eq := ?_
      integral := hintegral
      weight_le := hweight
      trace_eq := htrace
    }⟩
    rw [card_primeRootMultisetCanonicalEigenvalues]
    rfl

def TaoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        PrimeRootMultisetNewtonSpectrumConditions p χ R

theorem taoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore_iff_newtonConditions :
    TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore ↔
      TaoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact nonempty_primeKummerExplicitRootMultisetSpectrum_iff_newtonConditions.mp
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact nonempty_primeKummerExplicitRootMultisetSpectrum_iff_newtonConditions.mpr
      (h p χ R hχ hzero hone hcard hreduced)

end
end Tao2026

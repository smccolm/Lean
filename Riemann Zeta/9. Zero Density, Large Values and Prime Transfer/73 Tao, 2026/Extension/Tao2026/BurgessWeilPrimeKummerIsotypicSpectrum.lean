import Tao2026.BurgessWeilPrimeKummerAffineTrace

/-!
# The character-isotypic Kummer Frobenius spectrum

The affine Kummer cover contains one trace for every proper power of the
chosen multiplicative character.  An ordinary point-count estimate controls
their sum; the sharp Burgess input instead needs the single eigenspace on
which the deck group acts through the chosen character.

This file records that geometric input at its faithful spectral boundary.
The spectrum has at most `#roots - 1` eigenvalues, every eigenvalue has weight
at most one, and its negative trace is the required complete character sum.
The elementary triangle inequality then proves the sharp polynomial Kummer
bound and feeds the already completed prime-to-composite Burgess chain.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Every complex value of a finite-field multiplicative character is an
algebraic integer: it is either zero or a root of unity. -/
theorem isIntegral_mulChar_apply
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (x : ZMod p) :
    IsIntegral ℤ (χ x) := by
  by_cases hx : x = 0
  · subst x
    rw [MulChar.map_zero]
    exact isIntegral_zero
  · apply IsIntegral.of_pow χ.orderOf_pos
    obtain ⟨ζ, hζ, hζeq⟩ := χ.apply_mem_rootsOfUnity_orderOf hx
    rw [← hζeq, (mem_rootsOfUnity' (orderOf χ) ζ).mp hζ]
    exact isIntegral_one

/-- Complete finite-field polynomial character correlations are algebraic
integers. -/
theorem isIntegral_primePolynomialCharacterCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    IsIntegral ℤ (primePolynomialCharacterCorrelation p χ P) := by
  unfold primePolynomialCharacterCorrelation
  exact IsIntegral.sum (fun x => χ (P.eval x))
    (fun x _hx => isIntegral_mulChar_apply χ (P.eval x))

/-- Spectral data for the chosen-character eigenspace of a Kummer sheaf.

`rank_le` is the conductor/dimension estimate, `integral` records that genuine
Frobenius eigenvalues are algebraic integers, `weight_le` is the
Riemann-hypothesis weight-at-most-one assertion, and `trace_eq` is the
Grothendieck trace formula for the individual character sum.  The weight
inequality allows the weight-zero Jacobi degeneracies, while a rank smaller
than `#roots - 1` covers cancellation at infinity. -/
structure PrimeKummerIsotypicFrobeniusSpectrum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) where
  rank : ℕ
  eigenvalue : Fin rank → ℂ
  rank_le : rank ≤ P.roots.toFinset.card - 1
  integral : ∀ i, IsIntegral ℤ (eigenvalue i)
  weight_le : ∀ i, ‖eigenvalue i‖ ≤ Real.sqrt p
  trace_eq :
    primePolynomialCharacterCorrelation p χ P =
      -∑ i : Fin rank, eigenvalue i

/-- The rank and weight bounds of an isotypic Frobenius spectrum
give the sharp distinct-root Kummer estimate. -/
theorem PrimeKummerIsotypicFrobeniusSpectrum.correlation_norm_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSpectrum p χ P) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
  rw [s.trace_eq, norm_neg]
  calc
    ‖∑ i : Fin s.rank, s.eigenvalue i‖ ≤
        ∑ i : Fin s.rank, ‖s.eigenvalue i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin s.rank, Real.sqrt p :=
      Finset.sum_le_sum fun i _hi => s.weight_le i
    _ = (s.rank : ℝ) * Real.sqrt p := by simp
    _ ≤ ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg p)
      exact_mod_cast s.rank_le

/-- The genuine remaining geometric source proposition: every nondegenerate
split Kummer sheaf has a chosen-character Frobenius spectrum of weight at most
one and rank at most one less than the number of distinct roots. -/
def TaoPrimeKummerIsotypicFrobeniusSpectrum : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      Nonempty (PrimeKummerIsotypicFrobeniusSpectrum p χ P)

/-- The genuine non-elementary spectral residual, restricted to three or more
distinct roots. -/
def TaoPrimeKummerIsotypicFrobeniusSpectrumThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      3 ≤ P.roots.toFinset.card →
        Nonempty (PrimeKummerIsotypicFrobeniusSpectrum p χ P)

/-- The elementary Jacobi-sum theory constructs the isotypic spectrum for
every nondegenerate split polynomial with at most two distinct roots.  The
one-root trace is zero (rank zero); the two-root trace itself supplies the
single eigenvalue and the Jacobi estimate gives its weight bound. -/
theorem exists_primeKummerIsotypicFrobeniusSpectrum_of_card_roots_le_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits)
    (hroot : ∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a)
    (hcard : P.roots.toFinset.card ≤ 2) :
    Nonempty (PrimeKummerIsotypicFrobeniusSpectrum p χ P) := by
  have hsharp :
      ‖primePolynomialCharacterCorrelation p χ P‖ ≤
        ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
    rw [primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
    exact primeKummerRootCorrelation_le_of_card_roots_le_two
      p χ P hP hroot hcard
  obtain ⟨a, ha, _haActive⟩ := hroot
  have hcardPos : 0 < P.roots.toFinset.card :=
    Finset.card_pos.mpr ⟨a, ha⟩
  have hcases : P.roots.toFinset.card = 1 ∨
      P.roots.toFinset.card = 2 := by omega
  rcases hcases with hone | htwo
  · have hnormZero : ‖primePolynomialCharacterCorrelation p χ P‖ = 0 := by
      apply le_antisymm
      · simpa [hone] using hsharp
      · exact norm_nonneg _
    have hcorrZero : primePolynomialCharacterCorrelation p χ P = 0 :=
      norm_eq_zero.mp hnormZero
    exact ⟨{
      rank := 0
      eigenvalue := Fin.elim0
      rank_le := by simp [hone]
      integral := fun i => Fin.elim0 i
      weight_le := fun i => Fin.elim0 i
      trace_eq := by simp [hcorrZero] }⟩
  · exact ⟨{
      rank := 1
      eigenvalue := fun _ => -primePolynomialCharacterCorrelation p χ P
      rank_le := by simp [htwo]
      integral := fun _ =>
        (isIntegral_primePolynomialCharacterCorrelation p χ P).neg
      weight_le := by
        intro i
        simpa [htwo] using hsharp
      trace_eq := by simp }⟩

/-- Low-root existence in exactly the hypotheses used by the global Kummer
source proposition. -/
theorem exists_primeKummerIsotypicFrobeniusSpectrum_of_not_scalarPower_of_card_le_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hpower : ¬IsMulCharOrderScalarPower χ P)
    (hcard : P.roots.toFinset.card ≤ 2) :
    Nonempty (PrimeKummerIsotypicFrobeniusSpectrum p χ P) := by
  have hP0 : P ≠ 0 := by
    intro hzero
    subst P
    exact hpower (isMulCharOrderScalarPower_zero χ)
  have hroot :=
    (not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
      χ P hP0 hP).mp hpower
  exact exists_primeKummerIsotypicFrobeniusSpectrum_of_card_roots_le_two
    p χ P hP hroot hcard

/-- The spectral trace is literally the chosen multiplicative Fourier
coefficient of the scalar-twisted affine Kummer point counts. -/
theorem PrimeKummerIsotypicFrobeniusSpectrum.affineFourier_trace_eq
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSpectrum p χ P) (hχ : χ ≠ 1) :
    (∑ c : ZMod p,
        χ⁻¹ c * primeKummerAffineTraceDefect p χ P c) =
      -((p - 1 : ℕ) : ℂ) * ∑ i : Fin s.rank, s.eigenvalue i := by
  rw [sum_mulChar_inv_mul_primeKummerAffineTraceDefect p χ P hχ,
    s.trace_eq]
  ring

/-- The three-or-more-root spectral theorem supplies the full theorem because
the zero-, one-, and two-root cases are elementary. -/
theorem TaoPrimeKummerIsotypicFrobeniusSpectrumThreeRootsOrMore.toFull
    (hspec : TaoPrimeKummerIsotypicFrobeniusSpectrumThreeRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSpectrum := by
  intro p _ _ χ P hχ hP hpower
  by_cases hthree : 3 ≤ P.roots.toFinset.card
  · exact hspec p χ P hχ hP hpower hthree
  · exact
      exists_primeKummerIsotypicFrobeniusSpectrum_of_not_scalarPower_of_card_le_two
        p χ P hP hpower (by omega)

/-- Exact removal of the already proved low-root spectral cases. -/
theorem taoPrimeKummerIsotypicFrobeniusSpectrum_iff_threeRootsOrMore :
    TaoPrimeKummerIsotypicFrobeniusSpectrum ↔
      TaoPrimeKummerIsotypicFrobeniusSpectrumThreeRootsOrMore := by
  constructor
  · intro hspec p _ _ χ P hχ hP hpower _hthree
    exact hspec p χ P hχ hP hpower
  · exact
      TaoPrimeKummerIsotypicFrobeniusSpectrumThreeRootsOrMore.toFull

/-- The isotypic Frobenius theorem supplies the exact polynomial Kummer
estimate. -/
theorem TaoPrimeKummerIsotypicFrobeniusSpectrum.toPolynomial
    (hspec : TaoPrimeKummerIsotypicFrobeniusSpectrum) :
    TaoPrimeKummerPolynomialWeilBound := by
  intro p _ _ χ P hχ hP hpower
  exact (hspec p χ P hχ hP hpower).some.correlation_norm_le

/-- Direct prime-field bridge from the isotypic spectral theorem. -/
theorem TaoPrimeKummerIsotypicFrobeniusSpectrum.toLinearQuotient
    (hspec : TaoPrimeKummerIsotypicFrobeniusSpectrum) :
    TaoPrimeLinearQuotientWeilBound :=
  hspec.toPolynomial.toLinearQuotient

/-- Direct prime-to-composite bridge from the isotypic spectral theorem. -/
theorem TaoPrimeKummerIsotypicFrobeniusSpectrum.toComposite
    (hspec : TaoPrimeKummerIsotypicFrobeniusSpectrum) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hspec.toPolynomial.toComposite

/-- The Tao argument only consumes the fixed seventh Burgess moment.  The
isotypic theorem supplies that exact downstream endpoint as well. -/
theorem TaoPrimeKummerIsotypicFrobeniusSpectrum.toCompositeRSeven
    (hspec : TaoPrimeKummerIsotypicFrobeniusSpectrum) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  hspec.toComposite.toRSeven

/-- Direct fixed-moment Burgess bridge from the genuine non-elementary
three-or-more-root spectral residual. -/
theorem TaoPrimeKummerIsotypicFrobeniusSpectrumThreeRootsOrMore.toCompositeRSeven
    (hspec : TaoPrimeKummerIsotypicFrobeniusSpectrumThreeRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  hspec.toFull.toCompositeRSeven

end

end Tao2026

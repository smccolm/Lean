import Zeta23.PrimeSideB.PP

namespace PrimeShell

noncomputable section

open scoped BigOperators
open Set MeasureTheory Real
open Zeta23 Zeta23.PrimeSide

/-- The exact difference-frequency diagonal before the common `1 / (2 * π²)` factor. -/
def primeDiagonal (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n)

/-- The exact difference-frequency off-diagonal before the common `1 / (2 * π²)` factor. -/
def primeDifferenceOffDiagonal (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n = m then 0 else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m)

/-- The exact sum-frequency term before the common `1 / (2 * π²)` factor. -/
def primeSumFrequency (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)

/-- Exact resonant condition used for the Phase-I split.  It retains the literal logarithmic phase. -/
def IsPrimeResonant (T : ℝ) (n m : ℕ) : Prop :=
  |T * (Real.log n - Real.log m)| ≤ 1

instance (T : ℝ) (n m : ℕ) : Decidable (IsPrimeResonant T n m) :=
  Classical.propDecidable _

def primeResonantDifference (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n = m then 0 else if IsPrimeResonant T n m then
      acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m) else 0

def primeNonresonantDifference (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n = m then 0 else if IsPrimeResonant T n m then 0 else
      acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m)

theorem primeDifferenceOffDiagonal_eq_resonant_add_nonresonant
    (Φ : ℝ → ℝ) (T X : ℝ) :
    primeDifferenceOffDiagonal Φ T X =
      primeResonantDifference Φ T X + primeNonresonantDifference Φ T X := by
  unfold primeDifferenceOffDiagonal primeResonantDifference primeNonresonantDifference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hnm : n = m
  · simp [hnm]
  · by_cases hr : IsPrimeResonant T n m <;> simp [hnm, hr]

/-- Exact four-piece decomposition at the upstream equation-(5.12) level.
No estimate has been used. -/
theorem primePrime_exact_decomposition (hT : 0 ≤ T) (hΦ : Continuous Φ) (X : ℝ) :
    Mform Φ T (PX X) (PX X) =
      (1 / (2 * π ^ 2)) * primeDiagonal Φ T X +
      (1 / (2 * π ^ 2)) * primeResonantDifference Φ T X +
      (1 / (2 * π ^ 2)) * primeNonresonantDifference Φ T X +
      (1 / (2 * π ^ 2)) * primeSumFrequency Φ T X := by
  rw [Zeta23.PrimeSide.Mform_PX_PX hT hΦ]
  change (1 / (2 * π ^ 2)) *
      (primeDiagonal Φ T X + primeDifferenceOffDiagonal Φ T X +
        primeSumFrequency Φ T X) = _
  rw [primeDifferenceOffDiagonal_eq_resonant_add_nonresonant]
  ring

/-- The literal diagonal truncation error relative to the Fourier main term. -/
def primeDiagonalBoundary (Φ : ℝ → ℝ) (g : ℝ → ℝ) (T X : ℝ) : ℝ :=
  (1 / (2 * π ^ 2)) * primeDiagonal Φ T X - T / π * sumA2g X g

/-- Everything except the resonant difference-frequency contribution. -/
def primePrimeRemainder (Φ : ℝ → ℝ) (g : ℝ → ℝ) (T X : ℝ) : ℝ :=
  primeDiagonalBoundary Φ g T X +
    (1 / (2 * π ^ 2)) * primeNonresonantDifference Φ T X +
    (1 / (2 * π ^ 2)) * primeSumFrequency Φ T X

/-- Exact source-facing decomposition with the Fourier diagonal main term,
its boundary/truncation discrepancy, the resonant and nonresonant
difference-frequency pieces, and the opposite (sum-frequency) piece all
separately addressable. -/
theorem primePrime_exact_source_ledger
    (hT : 0 ≤ T) (hΦ : Continuous Φ) (g : ℝ → ℝ) (X : ℝ) :
    Mform Φ T (PX X) (PX X) =
      T / π * sumA2g X g +
      primeDiagonalBoundary Φ g T X +
      (1 / (2 * π ^ 2)) * primeResonantDifference Φ T X +
      (1 / (2 * π ^ 2)) * primeNonresonantDifference Φ T X +
      (1 / (2 * π ^ 2)) * primeSumFrequency Φ T X := by
  rw [primePrime_exact_decomposition hT hΦ]
  unfold primeDiagonalBoundary
  ring

theorem primePrime_sub_main_exact (hT : 0 ≤ T) (hΦ : Continuous Φ) (g : ℝ → ℝ) (X : ℝ) :
    Mform Φ T (PX X) (PX X) - T / π * sumA2g X g =
      (1 / (2 * π ^ 2)) * primeResonantDifference Φ T X +
      primePrimeRemainder Φ g T X := by
  rw [primePrime_exact_decomposition hT hΦ]
  unfold primePrimeRemainder primeDiagonalBoundary
  ring

/-- Regression form of Zeta23 Proposition 5.4.  The proof rewrites both the
upstream estimate and the requested conclusion through
`primePrime_exact_decomposition`, so the exact decomposition is on the checked
dependency path rather than merely being stated next to the old theorem. -/
theorem primePrime_bound_regression_from_exact_decomposition
    {cϱ lam : ℝ}
    (hcheb : Zeta23.ChebyshevMertens)
    (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (PX p.X) (PX p.X) - p.T / π * sumA2g p.X F.g|
        ≤ C * (p.L ^ 2 * p.X)) := by
  obtain ⟨C, T₀, hbound⟩ := Zeta23.PrimeSide.prop_PP hcheb hMV hlam
  refine ⟨C, max T₀ 0, fun p F hplam hT hF => ?_⟩
  have hT₀ : T₀ ≤ p.T := (le_max_left T₀ 0).trans hT
  have hpT : 0 ≤ p.T := (le_max_right T₀ 0).trans hT
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hold := hbound p F hplam hT₀ hF
  change |Mform F.Phi p.T (PX p.X) (PX p.X) - p.T / π * sumA2g p.X F.g|
      ≤ C * (p.L ^ 2 * p.X) at hold ⊢
  rw [primePrime_exact_decomposition hpT hΦ] at hold ⊢
  exact hold

end

end PrimeShell

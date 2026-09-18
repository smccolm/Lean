import Mathlib.FieldTheory.Finite.Trace
import Tao2026.BurgessWeilPrimeKummerIsotypicSpectrum

/-!
# The Kummer Frobenius power-trace system

A base-field trace and a finite family of bounded complex numbers do not by
themselves record Frobenius: once the desired norm estimate is known, the
whole trace can be placed in one eigenvalue.  Genuine Frobenius data use the
same eigenvalues over every finite extension, where degree `n` gives their
`n`th power sum.

This file defines the norm-lifted Kummer correlation over the canonical
finite extension of `ZMod p` and strengthens the isotypic spectrum by all of
its positive-degree power-trace identities.  Forgetting these identities
recovers the exact spectral input already connected to fixed-`r=7` Burgess.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The complete Kummer correlation over the degree-`n+1` extension of
`ZMod p`.  The base character is lifted by the field norm, as dictated by
the trace function of the base-changed Kummer sheaf. -/
def primeKummerExtensionCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : ℕ → ℂ
  | 0 => primePolynomialCharacterCorrelation p χ P
  | n + 1 => by
      let E := FiniteField.Extension (ZMod p) p (n + 2)
      letI : Fintype E := Fintype.ofFinite E
      exact ∑ x : E,
        χ (Algebra.norm (ZMod p)
          ((P.map (algebraMap (ZMod p) E)).eval x))

@[simp]
theorem primeKummerExtensionCorrelation_zero
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    primeKummerExtensionCorrelation p χ P 0 =
      primePolynomialCharacterCorrelation p χ P :=
  rfl

/-- A genuine chosen-character Frobenius system for a Kummer sheaf.

The underlying spectrum supplies the conductor, integrality, weight, and
base-field trace conditions.  `extensionTrace_eq` says that the very same
eigenvalues control every positive-degree extension correlation. -/
structure PrimeKummerIsotypicFrobeniusSystem
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    extends PrimeKummerIsotypicFrobeniusSpectrum p χ P where
  extensionTrace_eq : ∀ n : ℕ,
    primeKummerExtensionCorrelation p χ P n =
      -∑ i : Fin rank, eigenvalue i ^ (n + 1)

/-- Forgetting the extension power traces recovers the base-field spectrum. -/
def PrimeKummerIsotypicFrobeniusSystem.toSpectrum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ P) :
    PrimeKummerIsotypicFrobeniusSpectrum p χ P :=
  s.toPrimeKummerIsotypicFrobeniusSpectrum

/-- A rank-zero Frobenius system forces every extension correlation to
vanish. -/
theorem PrimeKummerIsotypicFrobeniusSystem.extensionCorrelation_eq_zero_of_rank_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ P) (hrank : s.rank = 0)
    (n : ℕ) : primeKummerExtensionCorrelation p χ P n = 0 := by
  rw [s.extensionTrace_eq n]
  have hsum : (∑ i : Fin s.rank, s.eigenvalue i ^ (n + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exfalso
    have hi := i.isLt
    omega
  rw [hsum]
  simp

/-- In rank one, consecutive extension traces obey a fixed geometric
recurrence.  This is already a genuine compatibility condition invisible in
the base-field spectrum alone. -/
theorem PrimeKummerIsotypicFrobeniusSystem.extensionCorrelation_succ_of_rank_eq_one
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ P) (hrank : s.rank = 1)
    (n : ℕ) :
    primeKummerExtensionCorrelation p χ P (n + 1) =
      -primePolynomialCharacterCorrelation p χ P *
        primeKummerExtensionCorrelation p χ P n := by
  classical
  let i0 : Fin s.rank := ⟨0, by omega⟩
  have hsum (f : Fin s.rank → ℂ) : ∑ i, f i = f i0 := by
    rw [Finset.sum_eq_single i0]
    · intro b _hb hne
      exact (hne (Fin.ext (by omega))).elim
    · simp
  rw [s.extensionTrace_eq (n + 1), s.extensionTrace_eq n, s.trace_eq,
    hsum, hsum, hsum]
  ring

/-- The genuine geometric source proposition, restricted to the only cases
not already handled by elementary one- and two-root character-sum theory. -/
def TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      3 ≤ P.roots.toFinset.card →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- The extension-compatible Frobenius theorem supplies the exact residual
base-field spectrum used by Burgess. -/
theorem TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore.toSpectrum
    (hsystem : TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSpectrumThreeRootsOrMore := by
  intro p _ _ χ P hχ hP hpower hroots
  exact (hsystem p χ P hχ hP hpower hroots).map
    PrimeKummerIsotypicFrobeniusSystem.toSpectrum

/-- Direct fixed-`r=7` Burgess transfer from the genuine all-extension
Frobenius source theorem. -/
theorem TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore.toCompositeRSeven
    (hsystem : TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  hsystem.toSpectrum.toCompositeRSeven

end

end Tao2026

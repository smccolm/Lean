import Tao2026.BurgessWeilPrimeKummerExtensionAffineTrace

/-!
# The affine-Fourier form of the Kummer Frobenius system

The extension-field Fourier identity turns the power-trace equations in
`PrimeKummerIsotypicFrobeniusSystem` into literal equations for scalar-twisted
affine Kummer point counts.  This file packages those geometric equations and
proves that, for a nontrivial character, they are exactly equivalent to the
original Frobenius-system contract.

The equivalence is lossless: the factor `p^(n+2)-1` is nonzero, so Fourier
normalization can be cancelled in every positive extension degree.  The
remaining three-or-more-root source theorem can therefore be stated entirely
as a bounded-rank, integral, weight-bounded decomposition of affine curve
point-count Fourier coefficients.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- A chosen-character Frobenius spectrum whose higher power traces are
stated directly as multiplicative Fourier coefficients of scalar-twisted
affine Kummer point-count defects. -/
structure PrimeKummerAffineFourierFrobeniusSystem
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    extends PrimeKummerIsotypicFrobeniusSpectrum p χ P where
  character_ne_one : χ ≠ 1
  higherAffineFourierTrace_eq : ∀ n : ℕ, by
    let E := FiniteField.Extension (ZMod p) p (n + 2)
    letI : Fintype E := Fintype.ofFinite E
    exact
      (∑ c : E,
        (finiteFieldNormLiftMulChar (ZMod p) E χ)⁻¹ c *
          primeKummerHigherExtensionAffineTraceDefect p χ P n c) =
        -((p ^ (n + 2) - 1 : ℕ) : ℂ) *
          ∑ i : Fin rank, eigenvalue i ^ (n + 2)

/-- Forget the affine Fourier equations and retain the base-field
spectrum. -/
def PrimeKummerAffineFourierFrobeniusSystem.toSpectrum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerAffineFourierFrobeniusSystem p χ P) :
    PrimeKummerIsotypicFrobeniusSpectrum p χ P :=
  s.toPrimeKummerIsotypicFrobeniusSpectrum

/-- Every genuine Kummer Frobenius system gives the corresponding geometric
affine-Fourier system. -/
def PrimeKummerIsotypicFrobeniusSystem.toAffineFourier
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ P) (hχ : χ ≠ 1) :
    PrimeKummerAffineFourierFrobeniusSystem p χ P where
  __ := s.toSpectrum
  character_ne_one := hχ
  higherAffineFourierTrace_eq := fun n => by
    dsimp
    rw [sum_normLift_inv_mul_primeKummerHigherExtensionAffineTraceDefect_eq_pow
      p χ P hχ n, s.extensionTrace_eq (n + 1)]
    simp only [PrimeKummerIsotypicFrobeniusSystem.toSpectrum]
    rw [show n + 1 + 1 = n + 2 by omega, mul_neg, neg_mul]
    rfl

/-- The positive Fourier normalization factor is nonzero. -/
theorem primeKummerHigherFourierNormalization_ne_zero
    (p n : ℕ) [Fact p.Prime] : p ^ (n + 2) - 1 ≠ 0 := by
  have hpow : 1 < p ^ (n + 2) :=
    one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  omega

/-- Cancelling the exact Fourier normalization reconstructs the original
all-extension power-trace system. -/
def PrimeKummerAffineFourierFrobeniusSystem.toFrobeniusSystem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerAffineFourierFrobeniusSystem p χ P) :
    PrimeKummerIsotypicFrobeniusSystem p χ P where
  __ := s.toSpectrum
  extensionTrace_eq := fun n => by
    cases n with
    | zero => simpa using s.trace_eq
    | succ n =>
      let E := FiniteField.Extension (ZMod p) p (n + 2)
      letI : Fintype E := Fintype.ofFinite E
      letI : DecidableEq E := Classical.decEq E
      let q : ℂ := (p ^ (n + 2) - 1 : ℕ)
      have hq : q ≠ 0 := by
        dsimp [q]
        exact_mod_cast primeKummerHigherFourierNormalization_ne_zero p n
      have hfourier :=
        sum_normLift_inv_mul_primeKummerHigherExtensionAffineTraceDefect_eq_pow
          p χ P s.character_ne_one n
      have hgeom := s.higherAffineFourierTrace_eq n
      apply mul_left_cancel₀ hq
      calc
        q * primeKummerExtensionCorrelation p χ P (n + 1) =
            ∑ c : E,
              (finiteFieldNormLiftMulChar (ZMod p) E χ)⁻¹ c *
                primeKummerHigherExtensionAffineTraceDefect p χ P n c :=
          hfourier.symm
        _ = -q * ∑ i : Fin s.rank, s.eigenvalue i ^ (n + 2) := hgeom
        _ = q * (-∑ i : Fin s.rank, s.eigenvalue i ^ (n + 2)) := by ring

/-- For a nontrivial character, the abstract power-trace system and the
affine point-count Fourier system exist simultaneously. -/
theorem nonempty_primeKummerIsotypicFrobeniusSystem_iff_affineFourier
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) (hχ : χ ≠ 1) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) ↔
      Nonempty (PrimeKummerAffineFourierFrobeniusSystem p χ P) := by
  constructor
  · exact fun hs => hs.map fun s => s.toAffineFourier hχ
  · exact fun hs => hs.map
      PrimeKummerAffineFourierFrobeniusSystem.toFrobeniusSystem

/-- The final geometric source proposition in literal affine point-count
Fourier form. -/
def TaoPrimeKummerAffineFourierFrobeniusSystemThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      3 ≤ P.roots.toFinset.card →
        Nonempty (PrimeKummerAffineFourierFrobeniusSystem p χ P)

/-- The three-or-more-root Frobenius theorem is exactly its affine
point-count Fourier formulation. -/
theorem taoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore_iff_affineFourier :
    TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore ↔
      TaoPrimeKummerAffineFourierFrobeniusSystemThreeRootsOrMore := by
  constructor
  · intro hsystem p _ _ χ P hχ hP hpower hroots
    exact (hsystem p χ P hχ hP hpower hroots).map
      (fun s => s.toAffineFourier hχ)
  · intro hsystem p _ _ χ P hχ hP hpower hroots
    exact (hsystem p χ P hχ hP hpower hroots).map
      PrimeKummerAffineFourierFrobeniusSystem.toFrobeniusSystem

/-- The affine-Fourier source theorem immediately gives the fixed-`r=7`
Burgess complete-sum input. -/
theorem TaoPrimeKummerAffineFourierFrobeniusSystemThreeRootsOrMore.toCompositeRSeven
    (hsystem : TaoPrimeKummerAffineFourierFrobeniusSystemThreeRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (taoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore_iff_affineFourier.mpr
    hsystem).toCompositeRSeven

end

end Tao2026

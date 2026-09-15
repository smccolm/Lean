import Tao2026.BurgessWeilPrimeTwelveRoots

/-!
# Source-specific residual for the prime Burgess sum

The generic split-polynomial Weil statement is much broader than the
polynomial actually produced by the Burgess quotient. This file packages the
successive source-specific large-characteristic residuals directly for
`primeLinearOrderPolynomial`. After the twelve-root reduction, the literal
`r = 7` path retains only the exact active-root window `13..14`; together with
the reduced lower-point inputs it still supplies the complete cube-free
Burgess endpoint.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The residual analytic input restricted to the exact cleared Burgess
polynomial.  All splitness, degree-divisibility, and tagged-root conditions
have already been proved internally for this polynomial family. -/
def TaoPrimeLinearOrderPolynomialWeilBoundFiveActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    5 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- After the five-active-root Möbius reduction, the source-specific analytic
input begins at six active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    6 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- After the six-active-root projective reduction, the exact source
residual begins at seven active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    7 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The seven-active-root source residual restricted to Tao's actual
fourteenth-moment order. -/
def TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristicRSeven : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    7 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- After the seven-active-root projective reduction, the source residual
begins at eight active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    8 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The eight-active-root residual at the sole production moment order. -/
def TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    8 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The literal remaining fixed-order source window: the cleared `r = 7`
polynomial can have at most fourteen distinct, hence active, roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundEightToFourteenActiveRootsLargeCharacteristicRSeven :
    Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    8 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- After the eight-active-root projective reduction, the source residual
begins at nine active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    9 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The nine-active-root residual at Tao's literal moment order `r = 7`. -/
def TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    9 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The narrowed literal fixed-order source window after closing exactly
eight active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundNineToFourteenActiveRootsLargeCharacteristicRSeven :
    Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    9 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- After the nine-active-root projective reduction, the source residual
begins at ten active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    10 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The ten-active-root residual at Tao's literal moment order `r = 7`. -/
def TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    10 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The narrowed literal fixed-order source window after closing exactly
nine active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundTenToFourteenActiveRootsLargeCharacteristicRSeven :
    Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    10 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- After the ten-active-root projective reduction, the source residual
begins at eleven active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    11 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The eleven-active-root residual at Tao's literal moment order `r = 7`. -/
def TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    11 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The narrowed literal fixed-order source window after closing exactly
ten active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundElevenToFourteenActiveRootsLargeCharacteristicRSeven :
    Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    11 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- After the eleven-active-root projective reduction, the source residual
begins at twelve active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    12 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The twelve-active-root residual at Tao's literal moment order `r = 7`. -/
def TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    12 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The narrowed literal fixed-order source window after closing exactly
eleven active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundTwelveToFourteenActiveRootsLargeCharacteristicRSeven :
    Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    12 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- After the twelve-active-root projective reduction, the source residual
begins at thirteen active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristic : Prop :=
  ∀ (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    13 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p r χ b)).card →
    4 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p r χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The thirteen-active-root residual at Tao's literal moment order `r = 7`. -/
def TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristicRSeven : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    13 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The narrowed literal fixed-order source window after closing exactly
twelve active roots. -/
def TaoPrimeLinearOrderPolynomialWeilBoundThirteenToFourteenActiveRootsLargeCharacteristicRSeven :
    Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    13 ≤ (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card →
    (primeActiveRoots p χ
      (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 →
    4 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ
      (primeLinearOrderPolynomial p 7 χ b)‖ ≤
      ((2 * (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card : ℕ) : ℝ) *
        Real.sqrt p

/-- The reduced three-parameter five-point power endpoint closes the exact
six-active-root source case. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic.toSixActiveRoots
    (hfive :
      TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic) :
    TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic := by
  intro p r _ _ χ b j hr hχ hunique hactiveSix hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 6
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p r χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p r (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
    have hrootCard : 6 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_six_degree_power
        p (hfive.toFivePoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveSixP : 6 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveSix
    have hactiveSevenP : 7 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p r χ b j hr hχ hunique
      (by simpa [P] using hactiveSevenP) hlarge

/-- The reduced two-parameter power endpoint closes the
exactly-five-active-root source case. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic.toFiveActiveRoots
    (hfour :
      TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic) :
    TaoPrimeLinearOrderPolynomialWeilBoundFiveActiveRootsLargeCharacteristic := by
  intro p r _ _ χ b j hr hχ hunique hactiveFive hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 5
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p r χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p r (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
    have hrootCard : 5 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_five_degree_power
        p (hfour.toFourPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveFiveP : 5 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveFive
    have hactiveSixP : 6 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p r χ b j hr hχ hunique
      (by simpa [P] using hactiveSixP) hlarge

/-- The canonical four-root hypergeometric estimate and the source-specific
five-root residual imply the original prime linear-quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundFiveActiveRootsLargeCharacteristic.toLinearQuotient
    (hhyper :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundFiveActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound := by
  intro p r _ χ b j hp hr hχ hunique
  letI : Fact p.Prime := ⟨hp⟩
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  have hP : P.Splits := by
    exact primeLinearOrderPolynomial_splits p r χ b
  have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) := by
    exact not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
      p r hp χ b j hχ hunique
  have hdegree : orderOf χ ∣ P.natDegree := by
    exact orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
  have hpoly :
      ‖primePolynomialCharacterCorrelation p χ P‖ ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    by_cases hsmall : p ≤ 4 * P.roots.toFinset.card ^ 2
    · exact primeSplitPolynomialWeilBound_of_prime_le_four_mul_card_sq
        p χ P hsmall
    · have hlarge : 4 * P.roots.toFinset.card ^ 2 < p := by omega
      by_cases hcardTwo : (primeActiveRoots p χ P).card ≤ 2
      · exact primeSplitPolynomialWeilBound_of_card_activeRoots_le_two
          p χ P (-b j) hχ hP hnot hcardTwo
      · by_cases hcardThree : (primeActiveRoots p χ P).card = 3
        · exact primeSplitPolynomialWeilBound_of_card_activeRoots_eq_three_degree
            p χ P (-b j) hχ hP hnot hdegree hcardThree
        · by_cases hcardFour : (primeActiveRoots p χ P).card = 4
          · have hrootCard : 4 ≤ P.roots.toFinset.card := by
              rw [← hcardFour]
              exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
            have hp64 : 64 < p := by nlinarith
            exact primeSplitPolynomialWeilBound_of_card_activeRoots_eq_four_degree_power
              p (hhyper.toThreePoint.toPower p hp64) χ P (-b j)
                hχ hP hnot hdegree hcardFour
          · have hactiveFive : 5 ≤ (primeActiveRoots p χ P).card := by omega
            exact hweil p r χ b j hr hχ hunique
              (by simpa [P] using hactiveFive)
              (by simpa [P] using hlarge)
  rw [primeLinearQuotientCorrelation_eq_polynomial p r χ b hχ]
  change ‖primePolynomialCharacterCorrelation p χ P‖ ≤ _
  calc
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hpoly
    _ ≤ ((4 * r : ℕ) : ℝ) * Real.sqrt p := by
      have hcard := card_roots_primeLinearOrderPolynomial_le p r hp χ b hχ
      have hnat : 2 * P.roots.toFinset.card ≤ 4 * r := by
        dsimp [P]
        omega
      have hreal :
          ((2 * P.roots.toFinset.card : ℕ) : ℝ) ≤ ((4 * r : ℕ) : ℝ) := by
        exact_mod_cast hnat
      exact mul_le_mul_of_nonneg_right hreal (Real.sqrt_nonneg p)

theorem TaoPrimeLinearOrderPolynomialWeilBoundFiveActiveRootsLargeCharacteristic.toComposite
    (hhyper :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundFiveActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hhyper).toComposite

/-- The reduced three-point endpoint, the reduced two-parameter four-point
power endpoint, and the source-specific six-active-root residual imply the
prime quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic.toLinearQuotient
    (hthree :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour :
      TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound :=
  (hweil.toFiveActiveRoots hfour).toLinearQuotient hthree

/-- Direct composite Burgess bridge from the six-active-root source residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic.toComposite
    (hthree :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour :
      TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hthree hfour).toComposite

/-- Direct prime-quotient bridge from the seven-active-root source residual
and the three reduced lower-point endpoints. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic.toLinearQuotient
    (hthree :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour :
      TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive :
      TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound :=
  (hweil.toSixActiveRoots hfive).toLinearQuotient hthree hfour

/-- Direct composite Burgess bridge from the seven-active-root source
residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic.toComposite
    (hthree :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour :
      TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive :
      TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hthree hfour hfive).toComposite

/-- The reduced four-parameter six-point endpoint closes the exactly-seven-
active-root source case. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristic.toSevenActiveRoots
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristic) :
    TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic := by
  intro p r _ _ χ b j hr hχ hunique hactiveSeven hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 7
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p r χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p r (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
    have hrootCard : 7 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_seven_degree_power
        p (hsix.toSixPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveSevenP : 7 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveSeven
    have hactiveEightP : 8 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p r χ b j hr hχ hunique
      (by simpa [P] using hactiveEightP) hlarge

/-- The reduced five-parameter seven-point endpoint closes the exactly-eight-
active-root source case. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristic.toEightActiveRoots
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristic) :
    TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristic := by
  intro p r _ _ χ b j hr hχ hunique hactiveEight hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 8
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p r χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p r (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
    have hrootCard : 8 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_eight_degree_power
        p (hseven.toSevenPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveEightP : 8 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveEight
    have hactiveNineP : 9 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p r χ b j hr hχ hunique
      (by simpa [P] using hactiveNineP) hlarge

/-- The reduced six-parameter eight-point endpoint closes the exactly-nine-
active-root source case. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristic.toNineActiveRoots
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristic) :
    TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristic := by
  intro p r _ _ χ b j hr hχ hunique hactiveNine hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 9
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p r χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p r (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
    have hrootCard : 9 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_nine_degree_power
        p (height.toEightPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveNineP : 9 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveNine
    have hactiveTenP : 10 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p r χ b j hr hχ hunique
      (by simpa [P] using hactiveTenP) hlarge

/-- The reduced seven-parameter nine-point endpoint closes the exactly-ten-
active-root source case. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristic.toTenActiveRoots
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristic) :
    TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristic := by
  intro p r _ _ χ b j hr hχ hunique hactiveTen hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 10
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p r χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p r (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
    have hrootCard : 10 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_ten_degree_power
        p (hnine.toNinePoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveTenP : 10 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveTen
    have hactiveElevenP : 11 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p r χ b j hr hχ hunique
      (by simpa [P] using hactiveElevenP) hlarge

/-- The four reduced lower-point endpoints and the eight-active-root source
residual imply the general prime quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristic.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound :=
  (hweil.toSevenActiveRoots hsix).toLinearQuotient hthree hfour hfive

/-- Direct composite bridge from the eight-active-root source residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristic.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hthree hfour hfive hsix).toComposite

/-- The five reduced lower-point endpoints and the nine-active-root residual
imply the general prime quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristic.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound :=
  (hweil.toEightActiveRoots hseven).toLinearQuotient hthree hfour hfive hsix

/-- Direct composite bridge from the nine-active-root source residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristic.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven).toComposite

/-- The six reduced endpoints and the ten-active-root residual imply the
general prime quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristic.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound :=
  (hweil.toNineActiveRoots height).toLinearQuotient hthree hfour hfive hsix hseven

/-- Direct composite bridge from the ten-active-root source residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristic.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height).toComposite

/-- The seven reduced endpoints and the eleven-active-root residual imply the
general prime quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristic.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound :=
  (hweil.toTenActiveRoots hnine).toLinearQuotient
    hthree hfour hfive hsix hseven height

/-- Direct composite bridge from the eleven-active-root source residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristic.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine).toComposite

/-- The fixed six-point endpoint closes exactly seven active roots on the
literal `r = 7` source path. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven.toSevenActiveRoots
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactiveSeven hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p 7 χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 7
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p 7 χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p 7 (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p 7 χ b
    have hrootCard : 7 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_seven_degree_power
        p (hsix.toSixPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveSevenP : 7 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveSeven
    have hactiveEightP : 8 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p χ b j hχ hunique
      (by simpa [P] using hactiveEightP) hlarge

/-- The fixed seven-point endpoint closes exactly eight active roots on the
literal `r = 7` source path. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven.toEightActiveRoots
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactiveEight hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p 7 χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 8
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p 7 χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p 7 (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p 7 χ b
    have hrootCard : 8 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_eight_degree_power
        p (hseven.toSevenPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveEightP : 8 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveEight
    have hactiveNineP : 9 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p χ b j hχ hunique
      (by simpa [P] using hactiveNineP) hlarge

/-- The fixed eight-point endpoint closes exactly nine active roots on the
literal `r = 7` source path. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven.toNineActiveRoots
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactiveNine hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p 7 χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 9
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p 7 χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p 7 (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p 7 χ b
    have hrootCard : 9 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_nine_degree_power
        p (height.toEightPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveNineP : 9 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveNine
    have hactiveTenP : 10 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p χ b j hχ hunique
      (by simpa [P] using hactiveTenP) hlarge

/-- The fixed nine-point endpoint closes exactly ten active roots on the
literal `r = 7` source path. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven.toTenActiveRoots
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactiveTen hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p 7 χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 10
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p 7 χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p 7 (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p 7 χ b
    have hrootCard : 10 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_ten_degree_power
        p (hnine.toNinePoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveTenP : 10 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveTen
    have hactiveElevenP : 11 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p χ b j hχ hunique
      (by simpa [P] using hactiveElevenP) hlarge

/-- At the actual moment order, the three reduced lower-point endpoints and
the seven-active-root source residual imply the fixed prime quotient bound. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour :
      TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive :
      TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven := by
  intro p _ χ b j hp hχ hunique
  letI : Fact p.Prime := ⟨hp⟩
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p 7 χ b
  have hP : P.Splits := by
    exact primeLinearOrderPolynomial_splits p 7 χ b
  have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) := by
    exact not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
      p 7 hp χ b j hχ hunique
  have hdegree : orderOf χ ∣ P.natDegree := by
    exact orderOf_dvd_natDegree_primeLinearOrderPolynomial p 7 χ b
  have hpoly :
      ‖primePolynomialCharacterCorrelation p χ P‖ ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    by_cases hsmall : p ≤ 4 * P.roots.toFinset.card ^ 2
    · exact primeSplitPolynomialWeilBound_of_prime_le_four_mul_card_sq
        p χ P hsmall
    · have hlarge : 4 * P.roots.toFinset.card ^ 2 < p := by omega
      by_cases hcardTwo : (primeActiveRoots p χ P).card ≤ 2
      · exact primeSplitPolynomialWeilBound_of_card_activeRoots_le_two
          p χ P (-b j) hχ hP hnot hcardTwo
      · by_cases hcardThree : (primeActiveRoots p χ P).card = 3
        · exact primeSplitPolynomialWeilBound_of_card_activeRoots_eq_three_degree
            p χ P (-b j) hχ hP hnot hdegree hcardThree
        · by_cases hcardFour : (primeActiveRoots p χ P).card = 4
          · have hrootCard : 4 ≤ P.roots.toFinset.card := by
              rw [← hcardFour]
              exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
            have hp64 : 64 < p := by nlinarith
            exact primeSplitPolynomialWeilBound_of_card_activeRoots_eq_four_degree_power
              p (hthree.toThreePoint.toPower p hp64) χ P (-b j)
                hχ hP hnot hdegree hcardFour
          · by_cases hcardFive : (primeActiveRoots p χ P).card = 5
            · have hrootCard : 5 ≤ P.roots.toFinset.card := by
                rw [← hcardFive]
                exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
              have hp64 : 64 < p := by nlinarith
              exact primeSplitPolynomialWeilBound_of_card_activeRoots_eq_five_degree_power
                p (hfour.toFourPoint.toPower p hp64) χ P (-b j)
                  hχ hP hnot hdegree hcardFive
            · by_cases hcardSix : (primeActiveRoots p χ P).card = 6
              · have hrootCard : 6 ≤ P.roots.toFinset.card := by
                  rw [← hcardSix]
                  exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
                have hp64 : 64 < p := by nlinarith
                exact primeSplitPolynomialWeilBound_of_card_activeRoots_eq_six_degree_power
                  p (hfive.toFivePoint.toPower p hp64) χ P (-b j)
                    hχ hP hnot hdegree hcardSix
              · have hactiveSeven : 7 ≤ (primeActiveRoots p χ P).card := by omega
                exact hweil p χ b j hχ hunique
                  (by simpa [P] using hactiveSeven)
                  (by simpa [P] using hlarge)
  rw [primeLinearQuotientCorrelation_eq_polynomial p 7 χ b hχ]
  change ‖primePolynomialCharacterCorrelation p χ P‖ ≤ _
  calc
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hpoly
    _ ≤ ((4 * 7 : ℕ) : ℝ) * Real.sqrt p := by
      have hcard := card_roots_primeLinearOrderPolynomial_le p 7 hp χ b hχ
      have hnat : 2 * P.roots.toFinset.card ≤ 4 * 7 := by
        dsimp [P]
        omega
      have hreal :
          ((2 * P.roots.toFinset.card : ℕ) : ℝ) ≤ ((4 * 7 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      exact mul_le_mul_of_nonneg_right hreal (Real.sqrt_nonneg p)

/-- The fixed source residual closes exactly the composite complete-sum
predicate consumed by Tao's final Burgess proof. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour :
      TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive :
      TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive).toComposite

/-- The exact finite window `8 ≤ active roots ≤ 14` supplies the fixed
eight-active-root residual because the cleared polynomial has at most
`2 * 7` distinct roots. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightToFourteenActiveRootsLargeCharacteristicRSeven.toEightActiveRoots
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundEightToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactive hlarge
  have hrootCard :
      (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ≤ 2 * 7 :=
    card_roots_primeLinearOrderPolynomial_le p 7 (Fact.out : p.Prime) χ b hχ
  have hactiveCard :
      (primeActiveRoots p χ
        (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 := by
    calc
      (primeActiveRoots p χ
          (primeLinearOrderPolynomial p 7 χ b)).card ≤
          (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card :=
        Finset.card_le_card (primeActiveRoots_subset_roots p χ _)
      _ ≤ 2 * 7 := hrootCard
      _ = 14 := by norm_num
  exact hweil p χ b j hχ hunique hactive hactiveCard hlarge

/-- The four reduced lower-point endpoints and the fixed eight-active-root
residual imply the literal `r = 7` prime quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  (hweil.toSevenActiveRoots hsix).toLinearQuotient hthree hfour hfive

/-- Direct fixed composite bridge from the eight-active-root source
residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix).toComposite

/-- Direct prime quotient bridge from the exact fixed source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightToFourteenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundEightToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  hweil.toEightActiveRoots.toLinearQuotient hthree hfour hfive hsix

/-- Direct fixed composite bridge from the exact `8..14` source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundEightToFourteenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundEightToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix).toComposite

/-- The exact finite window `9 ≤ active roots ≤ 14` supplies the fixed
nine-active-root residual; the upper bound is structural for `r = 7`. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineToFourteenActiveRootsLargeCharacteristicRSeven.toNineActiveRoots
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundNineToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactive hlarge
  have hrootCard :
      (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ≤ 2 * 7 :=
    card_roots_primeLinearOrderPolynomial_le p 7 (Fact.out : p.Prime) χ b hχ
  have hactiveCard :
      (primeActiveRoots p χ
        (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 := by
    calc
      (primeActiveRoots p χ
          (primeLinearOrderPolynomial p 7 χ b)).card ≤
          (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card :=
        Finset.card_le_card (primeActiveRoots_subset_roots p χ _)
      _ ≤ 2 * 7 := hrootCard
      _ = 14 := by norm_num
  exact hweil p χ b j hχ hunique hactive hactiveCard hlarge

/-- The five reduced endpoints and the fixed nine-active-root residual imply
the literal `r = 7` prime quotient bound. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  (hweil.toEightActiveRoots hseven).toLinearQuotient hthree hfour hfive hsix

/-- Direct fixed composite bridge from the nine-active-root residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundNineActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven).toComposite

/-- Direct prime quotient bridge from the narrowed exact source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineToFourteenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundNineToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  hweil.toNineActiveRoots.toLinearQuotient hthree hfour hfive hsix hseven

/-- Direct fixed composite bridge from the exact `9..14` source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundNineToFourteenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundNineToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven).toComposite

/-- The exact finite window `10 ≤ active roots ≤ 14` supplies the fixed
ten-active-root residual; the upper bound is structural for `r = 7`. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenToFourteenActiveRootsLargeCharacteristicRSeven.toTenActiveRoots
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundTenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactive hlarge
  have hrootCard :
      (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ≤ 2 * 7 :=
    card_roots_primeLinearOrderPolynomial_le p 7 (Fact.out : p.Prime) χ b hχ
  have hactiveCard :
      (primeActiveRoots p χ
        (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 := by
    calc
      (primeActiveRoots p χ
          (primeLinearOrderPolynomial p 7 χ b)).card ≤
          (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card :=
        Finset.card_le_card (primeActiveRoots_subset_roots p χ _)
      _ ≤ 2 * 7 := hrootCard
      _ = 14 := by norm_num
  exact hweil p χ b j hχ hunique hactive hactiveCard hlarge

/-- The six reduced endpoints and the fixed ten-active-root residual imply
the literal `r = 7` prime quotient bound. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  (hweil.toNineActiveRoots height).toLinearQuotient hthree hfour hfive hsix hseven

/-- Direct fixed composite bridge from the ten-active-root residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height).toComposite

/-- Direct prime quotient bridge from the narrowed exact source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenToFourteenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundTenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  hweil.toTenActiveRoots.toLinearQuotient hthree hfour hfive hsix hseven height

/-- Direct fixed composite bridge from the exact `10..14` source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTenToFourteenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundTenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height).toComposite

/-- The seven reduced endpoints and the fixed eleven-active-root residual imply
the literal `r = 7` prime quotient bound. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  (hweil.toTenActiveRoots hnine).toLinearQuotient
    hthree hfour hfive hsix hseven height

/-- Direct fixed composite bridge from the eleven-active-root residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine).toComposite

/-- The exact finite window `11 ≤ active roots ≤ 14` supplies the fixed
eleven-active-root residual; the upper bound is structural for `r = 7`. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenToFourteenActiveRootsLargeCharacteristicRSeven.toElevenActiveRoots
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundElevenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactive hlarge
  have hrootCard :
      (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ≤ 2 * 7 :=
    card_roots_primeLinearOrderPolynomial_le p 7 (Fact.out : p.Prime) χ b hχ
  have hactiveCard :
      (primeActiveRoots p χ
        (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 := by
    calc
      (primeActiveRoots p χ
          (primeLinearOrderPolynomial p 7 χ b)).card ≤
          (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card :=
        Finset.card_le_card (primeActiveRoots_subset_roots p χ _)
      _ ≤ 2 * 7 := hrootCard
      _ = 14 := by norm_num
  exact hweil p χ b j hχ hunique hactive hactiveCard hlarge

/-- Direct prime quotient bridge from the narrowed exact source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenToFourteenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundElevenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  hweil.toElevenActiveRoots.toLinearQuotient
    hthree hfour hfive hsix hseven height hnine

/-- Direct fixed composite bridge from the exact `11..14` source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundElevenToFourteenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundElevenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine).toComposite

/-- The reduced eight-parameter ten-point endpoint closes the exactly-eleven-
active-root source case. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristic.toElevenActiveRoots
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristic) :
    TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristic := by
  intro p r _ _ χ b j hr hχ hunique hactiveEleven hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 11
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p r χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p r (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
    have hrootCard : 11 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_eleven_degree_power
        p (hten.toTenPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveElevenP : 11 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveEleven
    have hactiveTwelveP : 12 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p r χ b j hr hχ hunique
      (by simpa [P] using hactiveTwelveP) hlarge

/-- The eight reduced endpoints and the twelve-active-root residual imply the
general prime quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristic.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound :=
  (hweil.toElevenActiveRoots hten).toLinearQuotient
    hthree hfour hfive hsix hseven height hnine

/-- Direct composite bridge from the twelve-active-root source residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristic.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine hten).toComposite

/-- The fixed ten-point endpoint closes exactly eleven active roots on the
literal `r = 7` source path. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven.toElevenActiveRoots
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundElevenActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactiveEleven hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p 7 χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 11
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p 7 χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p 7 (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p 7 χ b
    have hrootCard : 11 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_eleven_degree_power
        p (hten.toTenPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveElevenP : 11 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveEleven
    have hactiveTwelveP : 12 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p χ b j hχ hunique
      (by simpa [P] using hactiveTwelveP) hlarge

/-- The eight reduced endpoints and the fixed twelve-active-root residual imply
the literal `r = 7` prime quotient bound. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  (hweil.toElevenActiveRoots hten).toLinearQuotient
    hthree hfour hfive hsix hseven height hnine

/-- Direct fixed composite bridge from the twelve-active-root residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine hten).toComposite

/-- The reduced nine-parameter eleven-point endpoint closes the exactly-twelve-
active-root source case. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristic.toTwelveActiveRoots
    (heleven : TaoPrimeReducedPowerElevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristic) :
    TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristic := by
  intro p r _ _ χ b j hr hχ hunique hactiveTwelve hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p r χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 12
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p r χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p r (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p r χ b
    have hrootCard : 12 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_twelve_degree_power
        p (heleven.toElevenPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveTwelveP : 12 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveTwelve
    have hactiveThirteenP : 13 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p r χ b j hr hχ hunique
      (by simpa [P] using hactiveThirteenP) hlarge

/-- The nine reduced endpoints and the thirteen-active-root residual imply the
general prime quotient boundary. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristic.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (heleven : TaoPrimeReducedPowerElevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristic) :
    TaoPrimeLinearQuotientWeilBound :=
  (hweil.toTwelveActiveRoots heleven).toLinearQuotient
    hthree hfour hfive hsix hseven height hnine hten

/-- Direct composite bridge from the thirteen-active-root source residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristic.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (heleven : TaoPrimeReducedPowerElevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine hten heleven).toComposite

/-- The fixed eleven-point endpoint closes exactly twelve active roots on the
literal `r = 7` source path. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristicRSeven.toTwelveActiveRoots
    (heleven : TaoPrimeReducedPowerElevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactiveTwelve hlarge
  let P : Polynomial (ZMod p) := primeLinearOrderPolynomial p 7 χ b
  by_cases hcard : (primeActiveRoots p χ P).card = 12
  · have hP : P.Splits := primeLinearOrderPolynomial_splits p 7 χ b
    have hnot : ¬orderOf χ ∣ P.rootMultiplicity (-b j) :=
      not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
        p 7 (Fact.out : p.Prime) χ b j hχ hunique
    have hdegree : orderOf χ ∣ P.natDegree :=
      orderOf_dvd_natDegree_primeLinearOrderPolynomial p 7 χ b
    have hrootCard : 12 ≤ P.roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
    have hp64 : 64 < p := by nlinarith
    simpa [P] using
      (primeSplitPolynomialWeilBound_of_card_activeRoots_eq_twelve_degree_power
        p (heleven.toElevenPoint.toPower p hp64) χ P (-b j)
          hχ hP hnot hdegree hcard)
  · have hactiveTwelveP : 12 ≤ (primeActiveRoots p χ P).card := by
      simpa [P] using hactiveTwelve
    have hactiveThirteenP : 13 ≤ (primeActiveRoots p χ P).card := by omega
    exact hweil p χ b j hχ hunique
      (by simpa [P] using hactiveThirteenP) hlarge

/-- The nine reduced endpoints and the fixed thirteen-active-root residual
imply the literal `r = 7` prime quotient bound. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (heleven : TaoPrimeReducedPowerElevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  (hweil.toTwelveActiveRoots heleven).toLinearQuotient
    hthree hfour hfive hsix hseven height hnine hten

/-- Direct fixed composite bridge from the thirteen-active-root residual. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (heleven : TaoPrimeReducedPowerElevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil : TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine hten heleven).toComposite

/-- The exact finite window `12 ≤ active roots ≤ 14` supplies the fixed
twelve-active-root residual; the upper bound is structural for `r = 7`. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveToFourteenActiveRootsLargeCharacteristicRSeven.toTwelveActiveRoots
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundTwelveToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundTwelveActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactive hlarge
  have hrootCard :
      (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ≤ 2 * 7 :=
    card_roots_primeLinearOrderPolynomial_le p 7 (Fact.out : p.Prime) χ b hχ
  have hactiveCard :
      (primeActiveRoots p χ
        (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 := by
    calc
      (primeActiveRoots p χ
          (primeLinearOrderPolynomial p 7 χ b)).card ≤
          (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card :=
        Finset.card_le_card (primeActiveRoots_subset_roots p χ _)
      _ ≤ 2 * 7 := hrootCard
      _ = 14 := by norm_num
  exact hweil p χ b j hχ hunique hactive hactiveCard hlarge

/-- Direct prime quotient bridge from the narrowed exact source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveToFourteenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundTwelveToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  hweil.toTwelveActiveRoots.toLinearQuotient
    hthree hfour hfive hsix hseven height hnine hten

/-- Direct fixed composite bridge from the exact `12..14` source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundTwelveToFourteenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundTwelveToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine hten).toComposite

/-- The exact finite window `13 ≤ active roots ≤ 14` supplies the fixed
thirteen-active-root residual; the upper bound is structural for `r = 7`. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenToFourteenActiveRootsLargeCharacteristicRSeven.toThirteenActiveRoots
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundThirteenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearOrderPolynomialWeilBoundThirteenActiveRootsLargeCharacteristicRSeven := by
  intro p _ _ χ b j hχ hunique hactive hlarge
  have hrootCard :
      (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card ≤ 2 * 7 :=
    card_roots_primeLinearOrderPolynomial_le p 7 (Fact.out : p.Prime) χ b hχ
  have hactiveCard :
      (primeActiveRoots p χ
        (primeLinearOrderPolynomial p 7 χ b)).card ≤ 14 := by
    calc
      (primeActiveRoots p χ
          (primeLinearOrderPolynomial p 7 χ b)).card ≤
          (primeLinearOrderPolynomial p 7 χ b).roots.toFinset.card :=
        Finset.card_le_card (primeActiveRoots_subset_roots p χ _)
      _ ≤ 2 * 7 := hrootCard
      _ = 14 := by norm_num
  exact hweil p χ b j hχ hunique hactive hactiveCard hlarge

/-- Direct prime quotient bridge from the narrowed exact source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenToFourteenActiveRootsLargeCharacteristicRSeven.toLinearQuotient
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (heleven : TaoPrimeReducedPowerElevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundThirteenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimeLinearQuotientWeilBoundRSeven :=
  hweil.toThirteenActiveRoots.toLinearQuotient
    hthree hfour hfive hsix hseven height hnine hten heleven

/-- Direct fixed composite bridge from the exact `13..14` source window. -/
theorem TaoPrimeLinearOrderPolynomialWeilBoundThirteenToFourteenActiveRootsLargeCharacteristicRSeven.toComposite
    (hthree : TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour)
    (hfour : TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour)
    (hfive : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour)
    (hsix : TaoPrimeReducedPowerSixPointLegendreWeilBoundAboveSixtyFour)
    (hseven : TaoPrimeReducedPowerSevenPointLegendreWeilBoundAboveSixtyFour)
    (height : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour)
    (hnine : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour)
    (hten : TaoPrimeReducedPowerTenPointLegendreWeilBoundAboveSixtyFour)
    (heleven : TaoPrimeReducedPowerElevenPointLegendreWeilBoundAboveSixtyFour)
    (hweil :
      TaoPrimeLinearOrderPolynomialWeilBoundThirteenToFourteenActiveRootsLargeCharacteristicRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (hweil.toLinearQuotient hthree hfour hfive hsix hseven height hnine hten heleven).toComposite

end

end Tao2026

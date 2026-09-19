import Tao2026.BurgessWeilPrimeKummerReducedActivePolynomial

/-!
# Monic normalization of the reduced Kummer source

The leading coefficient in the remaining reduced-exponent Kummer theorem is
geometrically inessential.  Multiplication of a polynomial by a base scalar
multiplies its degree-`d` extension trace by the `d`th power of the scalar's
character value.  It can therefore be absorbed into every Frobenius
eigenvalue.

This file makes that transport exact.  Every nonzero polynomial is replaced
by its monic normalization `C leadingCoeff⁻¹ * P`; roots, multiplicities,
splitness, the reduced-exponent condition, rank, integrality, and the weight
bound are all preserved.  Consequently the final cohomological source is
equivalent to its restriction to monic split polynomials.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Multiplying a Kummer polynomial by a base-field scalar contributes the
corresponding character value to every Frobenius eigenvalue. -/
theorem primeKummerExtensionCorrelation_C_mul
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (c : ZMod p) (P : Polynomial (ZMod p)) :
    ∀ n : ℕ,
      primeKummerExtensionCorrelation p χ (Polynomial.C c * P) n =
        χ c ^ (n + 1) * primeKummerExtensionCorrelation p χ P n
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primeKummerExtensionCorrelation_zero,
        primePolynomialCharacterCorrelation_C_mul]
      simp
  | n + 1 => by
      rw [primeKummerExtensionCorrelation_succ_eq_normLift,
        primeKummerExtensionCorrelation_succ_eq_normLift]
      let d := n + 2
      letI : NeZero d := ⟨by omega⟩
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      letI : DecidableEq E := Classical.decEq E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      change finiteFieldPolynomialCharacterCorrelation E χE
          ((Polynomial.C c * P).map (algebraMap (ZMod p) E)) =
        χ c ^ (n + 1 + 1) *
          finiteFieldPolynomialCharacterCorrelation E χE
            (P.map (algebraMap (ZMod p) E))
      rw [Polynomial.map_mul, Polynomial.map_C,
        finiteFieldPolynomialCharacterCorrelation_C_mul,
        finiteFieldNormLiftMulChar_algebraMap_extension p d χ c]

/-- The explicit monic normalization used for the residual Kummer source. -/
def primeKummerMonicNormalization
    {p : ℕ} [NeZero p] (P : Polynomial (ZMod p)) :
    Polynomial (ZMod p) :=
  Polynomial.C P.leadingCoeff⁻¹ * P

/-- Monic normalization of a nonzero polynomial remains nonzero. -/
theorem primeKummerMonicNormalization_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP0 : P ≠ 0) :
    primeKummerMonicNormalization P ≠ 0 := by
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr
      (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP0))
  · exact hP0

/-- The normalization has leading coefficient one. -/
theorem primeKummerMonicNormalization_monic
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP0 : P ≠ 0) :
    (primeKummerMonicNormalization P).Monic := by
  rw [Polynomial.Monic, primeKummerMonicNormalization,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  exact inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hP0)

/-- Nonzero scalar normalization does not change the root multiset. -/
theorem roots_primeKummerMonicNormalization
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP0 : P ≠ 0) :
    (primeKummerMonicNormalization P).roots = P.roots := by
  rw [primeKummerMonicNormalization,
    Polynomial.roots_C_mul P
      (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP0))]

/-- In particular, the distinct root set is unchanged. -/
theorem roots_primeKummerMonicNormalization_toFinset
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP0 : P ≠ 0) :
    (primeKummerMonicNormalization P).roots.toFinset = P.roots.toFinset := by
  rw [roots_primeKummerMonicNormalization P hP0]

/-- Every root multiplicity survives monic normalization exactly. -/
theorem rootMultiplicity_primeKummerMonicNormalization
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP0 : P ≠ 0) (a : ZMod p) :
    (primeKummerMonicNormalization P).rootMultiplicity a =
      P.rootMultiplicity a := by
  rw [← Polynomial.count_roots,
    roots_primeKummerMonicNormalization P hP0,
    Polynomial.count_roots]

/-- Scalar normalization preserves splitness. -/
theorem primeKummerMonicNormalization_splits
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP : P.Splits) :
    (primeKummerMonicNormalization P).Splits := by
  exact hP.C_mul _

/-- Multiplying the normalization back by the leading coefficient recovers
the original polynomial. -/
theorem primeKummerMonicNormalization_reconstruct
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP0 : P ≠ 0) :
    Polynomial.C P.leadingCoeff * primeKummerMonicNormalization P = P := by
  rw [primeKummerMonicNormalization, ← mul_assoc, ← Polynomial.C_mul]
  simp [Polynomial.leadingCoeff_ne_zero.mpr hP0]

/-- The strict reduced-exponent property is invariant under monic
normalization. -/
theorem isPrimeKummerReducedExponentPolynomial_monicNormalization
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0)
    (hreduced : IsPrimeKummerReducedExponentPolynomial χ P) :
    IsPrimeKummerReducedExponentPolynomial χ
      (primeKummerMonicNormalization P) := by
  intro a ha
  rw [rootMultiplicity_primeKummerMonicNormalization P hP0 a]
  apply hreduced
  rwa [roots_primeKummerMonicNormalization_toFinset P hP0] at ha

/-- The full extension-trace sequence of a polynomial is the normalized
sequence twisted by the appropriate power of its leading coefficient. -/
theorem primeKummerExtensionCorrelation_eq_leadingCoeff_mul_monicNormalization
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) (n : ℕ) :
    primeKummerExtensionCorrelation p χ P n =
      χ P.leadingCoeff ^ (n + 1) *
        primeKummerExtensionCorrelation p χ
          (primeKummerMonicNormalization P) n := by
  conv_lhs => rw [← primeKummerMonicNormalization_reconstruct P hP0]
  exact primeKummerExtensionCorrelation_C_mul p χ P.leadingCoeff
    (primeKummerMonicNormalization P) n

/-- Absorb the leading-character scalar into each eigenvalue of a system for
the monic normalization.  Rank is unchanged, integrality is multiplicative,
and the scalar has norm at most one. -/
def PrimeKummerIsotypicFrobeniusSystem.twistLeadingCoeff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerMonicNormalization P)) (hP0 : P ≠ 0) :
    PrimeKummerIsotypicFrobeniusSystem p χ P where
  rank := s.rank
  eigenvalue i := χ P.leadingCoeff * s.eigenvalue i
  rank_le := by
    rw [← roots_primeKummerMonicNormalization_toFinset P hP0]
    exact s.rank_le
  integral i :=
    (isIntegral_mulChar_apply χ P.leadingCoeff).mul (s.integral i)
  weight_le i := by
    rw [norm_mul]
    calc
      ‖χ P.leadingCoeff‖ * ‖s.eigenvalue i‖ ≤
          1 * Real.sqrt p := by
        gcongr
        · exact DirichletCharacter.norm_le_one χ P.leadingCoeff
        · exact s.weight_le i
      _ = Real.sqrt p := one_mul _
  trace_eq := by
    change primeKummerExtensionCorrelation p χ P 0 =
      -∑ i : Fin s.rank, χ P.leadingCoeff * s.eigenvalue i
    rw [primeKummerExtensionCorrelation_eq_leadingCoeff_mul_monicNormalization
      p χ P hP0 0, s.extensionTrace_eq 0]
    simp only [Nat.zero_add, pow_one]
    rw [mul_neg, Finset.mul_sum]
  extensionTrace_eq n := by
    rw [primeKummerExtensionCorrelation_eq_leadingCoeff_mul_monicNormalization
      p χ P hP0 n, s.extensionTrace_eq n]
    simp_rw [mul_pow]
    rw [mul_neg, Finset.mul_sum]

/-- The final Kummer source restricted simultaneously to monic polynomials
and the strict finite exponent range. -/
def TaoPrimeKummerMonicReducedExponentFrobeniusSystemThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Monic → P.Splits →
      IsPrimeKummerReducedExponentPolynomial χ P →
      3 ≤ P.roots.toFinset.card →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- Allowing an arbitrary nonzero leading coefficient adds no content to the
reduced-exponent source theorem. -/
theorem taoPrimeKummerReducedExponentFrobeniusSystemThreeRootsOrMore_iff_monic :
    TaoPrimeKummerReducedExponentFrobeniusSystemThreeRootsOrMore ↔
      TaoPrimeKummerMonicReducedExponentFrobeniusSystemThreeRootsOrMore := by
  constructor
  · intro h p _ _ χ P hχ _hmonic hP hreduced hcard
    exact h p χ P hχ hP hreduced hcard
  · intro h p _ _ χ P hχ hP hreduced hcard
    have hP0 : P ≠ 0 := by
      intro hzero
      subst P
      simp at hcard
    let Q := primeKummerMonicNormalization P
    have hQmonic : Q.Monic :=
      primeKummerMonicNormalization_monic P hP0
    have hQsplits : Q.Splits :=
      primeKummerMonicNormalization_splits P hP
    have hQreduced : IsPrimeKummerReducedExponentPolynomial χ Q :=
      isPrimeKummerReducedExponentPolynomial_monicNormalization
        χ P hP0 hreduced
    have hQcard : 3 ≤ Q.roots.toFinset.card := by
      rwa [roots_primeKummerMonicNormalization_toFinset P hP0]
    exact (h p χ Q hχ hQmonic hQsplits hQreduced hQcard).map
      (fun s => s.twistLeadingCoeff hP0)

/-- The monic reduced source implies the complete Kummer Frobenius theorem. -/
theorem TaoPrimeKummerMonicReducedExponentFrobeniusSystemThreeRootsOrMore.toFull
    (hmonic :
      TaoPrimeKummerMonicReducedExponentFrobeniusSystemThreeRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerReducedExponentFrobeniusSystemThreeRootsOrMore.toFull
    (taoPrimeKummerReducedExponentFrobeniusSystemThreeRootsOrMore_iff_monic.mpr
      hmonic)

end

end Tao2026

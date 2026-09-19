import Tao2026.BurgessWeilPrimeKummerLegendreCharacteristic

/-!
# Canonical Legendre characteristic polynomial from two correlations

The trace and determinant of any two-element Legendre spectrum are already
forced by the first two explicit extension correlations.  This file defines
those coefficients directly from the finite-field sums and proves that every
Legendre spectrum has exactly the resulting quadratic Frobenius polynomial.

Consequently the entire spectral multiset is unique whenever it exists, and
the all-extension recurrence has coefficients containing no existential
eigenvalue choices.  The remaining Legendre problem is therefore existence
for one explicit quadratic polynomial, not construction of unspecified
spectral data.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The canonical trace coefficient, read from the base-field correlation. -/
def primePowerLegendreCharacteristicTrace
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : ℂ :=
  -primePowerLegendreExtensionCorrelation p χ m n k t 0

/-- The canonical determinant coefficient, recovered from the first two
power traces by the quadratic Newton identity. -/
def primePowerLegendreCharacteristicDeterminant
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : ℂ :=
  (primePowerLegendreExtensionCorrelation p χ m n k t 0 ^ 2 +
    primePowerLegendreExtensionCorrelation p χ m n k t 1) / 2

/-- The explicit canonical quadratic determined by the degree-one and
degree-two Legendre correlations. -/
def primePowerLegendreCharacteristicPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : Polynomial ℂ :=
  X ^ 2 - C (primePowerLegendreCharacteristicTrace p χ m n k t) * X +
    C (primePowerLegendreCharacteristicDeterminant p χ m n k t)

theorem PrimePowerLegendreSpectrum.eigenvalues_sum_eq_characteristicTrace
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.eigenvalues.sum =
      primePowerLegendreCharacteristicTrace p χ m n k t := by
  have h := s.trace_eq 0
  rw [sum_primePowerLegendreSpectrumEigenvalue_pow s 1,
    Fin.sum_univ_two] at h
  simp only [pow_one] at h
  rw [primePowerLegendreCharacteristicTrace, s.eigenvalues_sum]
  linear_combination h

theorem PrimePowerLegendreSpectrum.eigenvalues_prod_eq_characteristicDeterminant
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.eigenvalues.prod =
      primePowerLegendreCharacteristicDeterminant p χ m n k t := by
  have h0 := s.trace_eq 0
  rw [sum_primePowerLegendreSpectrumEigenvalue_pow s 1,
    Fin.sum_univ_two] at h0
  simp only [pow_one] at h0
  have h1 := s.trace_eq 1
  rw [sum_primePowerLegendreSpectrumEigenvalue_pow s 2,
    Fin.sum_univ_two] at h1
  rw [primePowerLegendreCharacteristicDeterminant,
    s.eigenvalues_prod, h0, h1]
  ring

theorem PrimePowerLegendreSpectrum.frobeniusPolynomial_eq_characteristicPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.frobeniusPolynomial =
      primePowerLegendreCharacteristicPolynomial p χ m n k t := by
  rw [s.frobeniusPolynomial_eq_quadratic,
    s.eigenvalues_sum_eq_characteristicTrace,
    s.eigenvalues_prod_eq_characteristicDeterminant]
  rfl

theorem primePowerLegendreCharacteristicPolynomial_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    (primePowerLegendreCharacteristicPolynomial p χ m n k t).roots =
      s.eigenvalues := by
  rw [← s.frobeniusPolynomial_eq_characteristicPolynomial,
    s.frobeniusPolynomial_roots]

theorem primePowerLegendreCharacteristicTrace_integral
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    IsIntegral ℤ (primePowerLegendreCharacteristicTrace p χ m n k t) := by
  rw [← s.eigenvalues_sum_eq_characteristicTrace]
  exact s.eigenvalues_sum_integral

theorem primePowerLegendreCharacteristicDeterminant_integral
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    IsIntegral ℤ
      (primePowerLegendreCharacteristicDeterminant p χ m n k t) := by
  rw [← s.eigenvalues_prod_eq_characteristicDeterminant]
  exact s.eigenvalues_prod_integral

theorem primePowerLegendreCharacteristicTrace_norm_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    ‖primePowerLegendreCharacteristicTrace p χ m n k t‖ ≤
      2 * Real.sqrt p := by
  let e := s.toEigenpair
  rw [← s.eigenvalues_sum_eq_characteristicTrace, s.eigenvalues_sum]
  calc
    ‖e.first + e.second‖ ≤ ‖e.first‖ + ‖e.second‖ := norm_add_le _ _
    _ ≤ Real.sqrt p + Real.sqrt p :=
      add_le_add e.weight_first e.weight_second
    _ = 2 * Real.sqrt p := by ring

theorem primePowerLegendreCharacteristicDeterminant_norm_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    ‖primePowerLegendreCharacteristicDeterminant p χ m n k t‖ ≤ p := by
  let e := s.toEigenpair
  rw [← s.eigenvalues_prod_eq_characteristicDeterminant,
    s.eigenvalues_prod, norm_mul]
  calc
    ‖e.first‖ * ‖e.second‖ ≤ Real.sqrt p * Real.sqrt p := by
      exact mul_le_mul e.weight_first e.weight_second (norm_nonneg _)
        (Real.sqrt_nonneg _)
    _ = p := by
      rw [← sq]
      exact Real.sq_sqrt (Nat.cast_nonneg p)

theorem PrimePowerLegendreSpectrum.trace_recurrence_characteristic
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) (q : ℕ) :
    primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
      primePowerLegendreCharacteristicTrace p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
        primePowerLegendreCharacteristicDeterminant p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t q := by
  rw [s.trace_recurrence,
    s.eigenvalues_sum_eq_characteristicTrace,
    s.eigenvalues_prod_eq_characteristicDeterminant]

theorem primePowerLegendreSpectrum_eigenvalues_unique
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s₁ s₂ : PrimePowerLegendreSpectrum p χ m n k t) :
    s₁.eigenvalues = s₂.eigenvalues := by
  rw [← primePowerLegendreCharacteristicPolynomial_roots s₁,
    ← primePowerLegendreCharacteristicPolynomial_roots s₂]

theorem primePowerLegendreSpectrum_unique
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s₁ s₂ : PrimePowerLegendreSpectrum p χ m n k t) : s₁ = s₂ := by
  cases s₁ with
  | mk eigenvalues₁ card₁ integral₁ weight₁ trace₁ =>
    cases s₂ with
    | mk eigenvalues₂ card₂ integral₂ weight₂ trace₂ =>
      have h : eigenvalues₁ = eigenvalues₂ :=
        primePowerLegendreSpectrum_eigenvalues_unique
          ⟨eigenvalues₁, card₁, integral₁, weight₁, trace₁⟩
          ⟨eigenvalues₂, card₂, integral₂, weight₂, trace₂⟩
      cases h
      rfl

instance instSubsingletonPrimePowerLegendreSpectrum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p} :
    Subsingleton (PrimePowerLegendreSpectrum p χ m n k t) :=
  ⟨primePowerLegendreSpectrum_unique⟩

end
end Tao2026

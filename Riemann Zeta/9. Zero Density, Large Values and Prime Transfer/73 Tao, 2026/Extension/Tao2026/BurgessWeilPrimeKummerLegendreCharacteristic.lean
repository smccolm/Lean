import Tao2026.BurgessWeilPrimeKummerLegendreSpectrum

/-!
# Intrinsic quadratic characteristic data for the Legendre spectrum

A two-element Legendre spectrum has canonical trace and determinant: the sum
and product of its unordered eigenvalue multiset.  This file identifies those
symmetric quantities with any fixed enumeration, proves that they are integral,
expands the canonical Frobenius polynomial as the corresponding monic
quadratic, and derives the order-two recurrence for all extension traces.

Thus neither the characteristic polynomial nor the recurrence depends on a
choice of ordering for the two eigenvalues.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

theorem PrimePowerLegendreSpectrum.eigenvalues_sum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.eigenvalues.sum =
      primePowerLegendreSpectrumEigenvalue s 0 +
        primePowerLegendreSpectrumEigenvalue s 1 := by
  have h := sum_primePowerLegendreSpectrumEigenvalue_pow s 1
  rw [Fin.sum_univ_two] at h
  simpa using h

theorem PrimePowerLegendreSpectrum.eigenvalues_prod
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.eigenvalues.prod =
      primePowerLegendreSpectrumEigenvalue s 0 *
        primePowerLegendreSpectrumEigenvalue s 1 := by
  let l := primeKummerSpectralList s.eigenvalues
  have hlen : l.length = 2 :=
    (length_primeKummerSpectralList s.eigenvalues).trans s.card_eq
  let e : Fin 2 ≃ Fin l.length := (Fin.castOrderIso hlen.symm).toEquiv
  calc
    s.eigenvalues.prod = (↑l : Multiset ℂ).prod := by
      rw [coe_primeKummerSpectralList]
    _ = l.prod := Multiset.prod_coe l
    _ = (List.ofFn l.get).prod := by rw [List.ofFn_get]
    _ = ∏ j : Fin l.length, l.get j := List.prod_ofFn
    _ = ∏ i : Fin 2, primePowerLegendreSpectrumEigenvalue s i := by
      symm
      simpa [primePowerLegendreSpectrumEigenvalue, l, e] using
        (Equiv.prod_comp e (fun j : Fin l.length => l.get j))
    _ = primePowerLegendreSpectrumEigenvalue s 0 *
        primePowerLegendreSpectrumEigenvalue s 1 := Fin.prod_univ_two _

theorem PrimePowerLegendreSpectrum.frobeniusPolynomial_eq_product_eigenvalues
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.frobeniusPolynomial =
      ∏ i : Fin 2, (X - C (primePowerLegendreSpectrumEigenvalue s i)) := by
  let l := primeKummerSpectralList s.eigenvalues
  have hlen : l.length = 2 :=
    (length_primeKummerSpectralList s.eigenvalues).trans s.card_eq
  let e : Fin 2 ≃ Fin l.length := (Fin.castOrderIso hlen.symm).toEquiv
  calc
    s.frobeniusPolynomial =
        ((↑l : Multiset ℂ).map fun a => X - C a).prod := by
      unfold PrimePowerLegendreSpectrum.frobeniusPolynomial
      rw [coe_primeKummerSpectralList]
    _ = (List.map (fun a : ℂ => X - C a) l).prod := by
      rw [Multiset.map_coe, Multiset.prod_coe]
    _ = (List.ofFn (fun j : Fin l.length => X - C (l.get j))).prod := by
      congr 1
      calc
        List.map (fun a : ℂ => X - C a) l =
            List.map (fun a : ℂ => X - C a) (List.ofFn l.get) := by
          rw [List.ofFn_get]
        _ = List.ofFn (fun j : Fin l.length => X - C (l.get j)) := by
          rw [List.map_ofFn]
          rfl
    _ = ∏ j : Fin l.length, (X - C (l.get j)) := List.prod_ofFn
    _ = ∏ i : Fin 2,
        (X - C (primePowerLegendreSpectrumEigenvalue s i)) := by
      symm
      simpa [primePowerLegendreSpectrumEigenvalue, l, e] using
        (Equiv.prod_comp e (fun j : Fin l.length => X - C (l.get j)))

theorem PrimePowerLegendreSpectrum.frobeniusPolynomial_eq_quadratic
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.frobeniusPolynomial =
      X ^ 2 - C s.eigenvalues.sum * X + C s.eigenvalues.prod := by
  rw [s.frobeniusPolynomial_eq_product_eigenvalues, Fin.prod_univ_two,
    s.eigenvalues_sum, s.eigenvalues_prod]
  simp only [map_add, map_mul]
  ring

theorem PrimePowerLegendreSpectrum.eigenvalues_sum_integral
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    IsIntegral ℤ s.eigenvalues.sum := by
  rw [s.eigenvalues_sum]
  exact s.toEigenpair.integral_first.add s.toEigenpair.integral_second

theorem PrimePowerLegendreSpectrum.eigenvalues_prod_integral
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    IsIntegral ℤ s.eigenvalues.prod := by
  rw [s.eigenvalues_prod]
  exact s.toEigenpair.integral_first.mul s.toEigenpair.integral_second

theorem PrimePowerLegendreSpectrum.trace_recurrence
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) (q : ℕ) :
    primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
      s.eigenvalues.sum *
          primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
        s.eigenvalues.prod *
          primePowerLegendreExtensionCorrelation p χ m n k t q := by
  let e := s.toEigenpair
  rw [s.eigenvalues_sum, s.eigenvalues_prod]
  exact e.trace_recurrence q

end
end Tao2026

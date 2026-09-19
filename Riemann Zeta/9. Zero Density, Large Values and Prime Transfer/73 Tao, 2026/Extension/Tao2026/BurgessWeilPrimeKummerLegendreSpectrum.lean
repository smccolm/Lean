import Tao2026.BurgessWeilPrimeKummerRootMultisetSpectrum

/-!
# Intrinsic Legendre Frobenius spectra

The Legendre eigenpair chooses an ordering of its two eigenvalues.  This file
replaces the pair by an intrinsic two-element spectral multiset and proves the
two formulations equivalent, including every extension power trace.

The spectrum defines a canonical monic split quadratic Frobenius polynomial.
Together with the higher-root spectrum, this puts both remaining geometric
branches into the same unordered spectral form.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

structure PrimePowerLegendreSpectrum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) where
  eigenvalues : Multiset ℂ
  card_eq : eigenvalues.card = 2
  integral : ∀ a ∈ eigenvalues, IsIntegral ℤ a
  weight_le : ∀ a ∈ eigenvalues, ‖a‖ ≤ Real.sqrt p
  trace_eq : ∀ q : ℕ,
    primePowerLegendreExtensionCorrelation p χ m n k t q =
      -(eigenvalues.map fun a => a ^ (q + 1)).sum

def PrimePowerLegendreSpectrum.frobeniusPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) : Polynomial ℂ :=
  (s.eigenvalues.map fun a => X - C a).prod

theorem PrimePowerLegendreSpectrum.frobeniusPolynomial_monic
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.frobeniusPolynomial.Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C s.eigenvalues

theorem PrimePowerLegendreSpectrum.frobeniusPolynomial_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.frobeniusPolynomial.roots = s.eigenvalues := by
  exact Polynomial.roots_multiset_prod_X_sub_C s.eigenvalues

theorem PrimePowerLegendreSpectrum.frobeniusPolynomial_splits
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.frobeniusPolynomial.Splits := by
  apply Polynomial.Splits.multisetProd
  intro f hf
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hf
  exact Polynomial.Splits.X_sub_C a

theorem PrimePowerLegendreSpectrum.frobeniusPolynomial_natDegree
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    s.frobeniusPolynomial.natDegree = 2 := by
  rw [s.frobeniusPolynomial_splits.natDegree_eq_card_roots,
    s.frobeniusPolynomial_roots, s.card_eq]

theorem PrimePowerLegendreSpectrum.trace_eq_frobeniusPolynomial_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) (q : ℕ) :
    primePowerLegendreExtensionCorrelation p χ m n k t q =
      -(s.frobeniusPolynomial.roots.map fun a => a ^ (q + 1)).sum := by
  rw [s.frobeniusPolynomial_roots]
  exact s.trace_eq q

def PrimePowerLegendreEigenpair.toSpectrum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (e : PrimePowerLegendreEigenpair p χ m n k t) :
    PrimePowerLegendreSpectrum p χ m n k t where
  eigenvalues := e.first ::ₘ e.second ::ₘ 0
  card_eq := by simp
  integral a ha := by
    simp at ha
    rcases ha with rfl | rfl
    · exact e.integral_first
    · exact e.integral_second
  weight_le a ha := by
    simp at ha
    rcases ha with rfl | rfl
    · exact e.weight_first
    · exact e.weight_second
  trace_eq q := by
    rw [e.trace_eq q]
    simp [add_comm]

def primePowerLegendreSpectrumEigenvalue
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) (i : Fin 2) : ℂ :=
  (primeKummerSpectralList s.eigenvalues).get
    ⟨i.val, by rw [length_primeKummerSpectralList, s.card_eq]; exact i.isLt⟩

theorem sum_primePowerLegendreSpectrumEigenvalue_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) (d : ℕ) :
    (s.eigenvalues.map fun a => a ^ d).sum =
      ∑ i : Fin 2, primePowerLegendreSpectrumEigenvalue s i ^ d := by
  let l := primeKummerSpectralList s.eigenvalues
  have hlen : l.length = 2 :=
    (length_primeKummerSpectralList s.eigenvalues).trans s.card_eq
  let e : Fin 2 ≃ Fin l.length := (Fin.castOrderIso hlen.symm).toEquiv
  calc
    (s.eigenvalues.map fun a => a ^ d).sum =
        ((↑l : Multiset ℂ).map fun a => a ^ d).sum := by
      rw [coe_primeKummerSpectralList]
    _ = (List.map (fun a => a ^ d) l).sum := by
      rw [Multiset.map_coe, Multiset.sum_coe]
    _ = (List.ofFn (fun j : Fin l.length => l.get j ^ d)).sum := by
      congr 1
      calc
        List.map (fun a => a ^ d) l =
            List.map (fun a => a ^ d) (List.ofFn l.get) := by
          rw [List.ofFn_get]
        _ = List.ofFn (fun j : Fin l.length => l.get j ^ d) := by
          rw [List.map_ofFn]
          rfl
    _ = ∑ j : Fin l.length, l.get j ^ d := List.sum_ofFn
    _ = ∑ i : Fin 2, primePowerLegendreSpectrumEigenvalue s i ^ d := by
      symm
      simpa [primePowerLegendreSpectrumEigenvalue, l, e] using
        (Equiv.sum_comp e (fun j : Fin l.length => l.get j ^ d))

def PrimePowerLegendreSpectrum.toEigenpair
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) :
    PrimePowerLegendreEigenpair p χ m n k t where
  first := primePowerLegendreSpectrumEigenvalue s 0
  second := primePowerLegendreSpectrumEigenvalue s 1
  integral_first := by
    apply s.integral
    rw [← coe_primeKummerSpectralList s.eigenvalues, Multiset.mem_coe]
    exact List.get_mem _ _
  integral_second := by
    apply s.integral
    rw [← coe_primeKummerSpectralList s.eigenvalues, Multiset.mem_coe]
    exact List.get_mem _ _
  weight_first := by
    apply s.weight_le
    rw [← coe_primeKummerSpectralList s.eigenvalues, Multiset.mem_coe]
    exact List.get_mem _ _
  weight_second := by
    apply s.weight_le
    rw [← coe_primeKummerSpectralList s.eigenvalues, Multiset.mem_coe]
    exact List.get_mem _ _
  trace_eq q := by
    rw [s.trace_eq q, sum_primePowerLegendreSpectrumEigenvalue_pow s (q + 1),
      Fin.sum_univ_two]

theorem nonempty_primePowerLegendreEigenpair_iff_spectrum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p} :
    Nonempty (PrimePowerLegendreEigenpair p χ m n k t) ↔
      Nonempty (PrimePowerLegendreSpectrum p χ m n k t) := by
  constructor
  · exact fun h => h.map PrimePowerLegendreEigenpair.toSpectrum
  · exact fun h => h.map PrimePowerLegendreSpectrum.toEigenpair

theorem PrimePowerLegendreSpectrum.extension_norm_le_two_mul_sqrt_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p}
    (s : PrimePowerLegendreSpectrum p χ m n k t) (q : ℕ) :
    ‖primePowerLegendreExtensionCorrelation p χ m n k t q‖ ≤
      2 * Real.sqrt p ^ (q + 1) := by
  let e := s.toEigenpair
  rw [e.trace_eq q, norm_neg]
  calc
    ‖e.first ^ (q + 1) + e.second ^ (q + 1)‖ ≤
        ‖e.first ^ (q + 1)‖ + ‖e.second ^ (q + 1)‖ := norm_add_le _ _
    _ ≤ Real.sqrt p ^ (q + 1) + Real.sqrt p ^ (q + 1) := by
      rw [norm_pow, norm_pow]
      exact add_le_add
        (pow_le_pow_left₀ (norm_nonneg _) e.weight_first _)
        (pow_le_pow_left₀ (norm_nonneg _) e.weight_second _)
    _ = 2 * Real.sqrt p ^ (q + 1) := by ring

def TaoPrimePowerLegendreSpectrum : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        Nonempty (PrimePowerLegendreSpectrum p χ m n k t)

theorem taoPrimePowerLegendreEigenpair_iff_spectrum :
    TaoPrimePowerLegendreEigenpair ↔ TaoPrimePowerLegendreSpectrum := by
  constructor
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact nonempty_primePowerLegendreEigenpair_iff_spectrum.mp
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact nonempty_primePowerLegendreEigenpair_iff_spectrum.mpr
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)

def TaoPrimeExplicitLegendreAndRootMultisetSpectra : Prop :=
  TaoPrimePowerLegendreSpectrum ∧
    TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore

theorem taoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum_iff_bothSpectra :
    TaoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum ↔
      TaoPrimeExplicitLegendreAndRootMultisetSpectra := by
  rw [TaoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum,
    TaoPrimeExplicitLegendreAndRootMultisetSpectra,
    taoPrimePowerLegendreEigenpair_iff_spectrum]

theorem TaoPrimeExplicitLegendreAndRootMultisetSpectra.toFull
    (h : TaoPrimeExplicitLegendreAndRootMultisetSpectra) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum.toFull
    (taoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum_iff_bothSpectra.mpr h)

end
end Tao2026

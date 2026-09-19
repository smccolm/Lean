import Tao2026.BurgessWeilPrimeKummerRootMultisetCorrelation

/-!
# Unordered higher-root Frobenius spectra

The explicit higher-root eigenvalue vector still chooses an arbitrary order.
This file replaces it by the intrinsic multiset of Frobenius eigenvalues,
with cardinality exactly one less than the root-support cardinality.

The vector and multiset formulations are equivalent, including repeated
eigenvalues and every power trace.  The spectral multiset also produces its
canonical monic split Frobenius polynomial, whose roots are exactly the
spectrum and whose degree is exactly the conductor bound.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def primeKummerSpectralList {α : Type*} (A : Multiset α) : List α :=
  Quotient.out A

theorem coe_primeKummerSpectralList {α : Type*} (A : Multiset α) :
    (↑(primeKummerSpectralList A) : Multiset α) = A := by
  exact Quotient.out_eq A

theorem length_primeKummerSpectralList {α : Type*} (A : Multiset α) :
    (primeKummerSpectralList A).length = A.card := by
  have h := congrArg Multiset.card (coe_primeKummerSpectralList A)
  simpa using h

structure PrimeKummerExplicitRootMultisetSpectrum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) where
  eigenvalues : Multiset ℂ
  card_eq : eigenvalues.card = R.toFinset.card - 1
  integral : ∀ a ∈ eigenvalues, IsIntegral ℤ a
  weight_le : ∀ a ∈ eigenvalues, ‖a‖ ≤ Real.sqrt p
  trace_eq : ∀ q : ℕ,
    primeRootMultisetExtensionCorrelation p χ R q =
      -(eigenvalues.map fun a => a ^ (q + 1)).sum

def PrimeKummerExplicitRootMultisetSpectrum.frobeniusPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) : Polynomial ℂ :=
  (s.eigenvalues.map fun a => X - C a).prod

theorem PrimeKummerExplicitRootMultisetSpectrum.frobeniusPolynomial_monic
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    s.frobeniusPolynomial.Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C s.eigenvalues

theorem PrimeKummerExplicitRootMultisetSpectrum.frobeniusPolynomial_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    s.frobeniusPolynomial.roots = s.eigenvalues := by
  exact Polynomial.roots_multiset_prod_X_sub_C s.eigenvalues

theorem PrimeKummerExplicitRootMultisetSpectrum.frobeniusPolynomial_splits
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    s.frobeniusPolynomial.Splits := by
  apply Polynomial.Splits.multisetProd
  intro f hf
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hf
  exact Polynomial.Splits.X_sub_C a

theorem PrimeKummerExplicitRootMultisetSpectrum.frobeniusPolynomial_natDegree
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    s.frobeniusPolynomial.natDegree = R.toFinset.card - 1 := by
  rw [s.frobeniusPolynomial_splits.natDegree_eq_card_roots,
    s.frobeniusPolynomial_roots, s.card_eq]

theorem PrimeKummerExplicitRootMultisetSpectrum.trace_eq_frobeniusPolynomial_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) (q : ℕ) :
    primeRootMultisetExtensionCorrelation p χ R q =
      -(s.frobeniusPolynomial.roots.map fun a => a ^ (q + 1)).sum := by
  rw [s.frobeniusPolynomial_roots]
  exact s.trace_eq q

def PrimeKummerExplicitRootMultisetEigenvalues.toSpectrum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (e : PrimeKummerExplicitRootMultisetEigenvalues p χ R) :
    PrimeKummerExplicitRootMultisetSpectrum p χ R where
  eigenvalues := ↑(List.ofFn e.eigenvalue)
  card_eq := by simp
  integral a ha := by
    rw [Multiset.mem_coe, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact e.integral i
  weight_le a ha := by
    rw [Multiset.mem_coe, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact e.weight_le i
  trace_eq q := by
    rw [e.trace_eq q]
    congr 1
    simp [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn,
      List.sum_ofFn]

def primeKummerRootMultisetSpectrumEigenvalue
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R)
    (i : Fin (R.toFinset.card - 1)) : ℂ :=
  (primeKummerSpectralList s.eigenvalues).get
    ⟨i.val, by rw [length_primeKummerSpectralList, s.card_eq]; exact i.isLt⟩

def PrimeKummerExplicitRootMultisetSpectrum.toEigenvalues
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) :
    PrimeKummerExplicitRootMultisetEigenvalues p χ R where
  eigenvalue := primeKummerRootMultisetSpectrumEigenvalue s
  integral i := by
    apply s.integral
    rw [← coe_primeKummerSpectralList s.eigenvalues, Multiset.mem_coe]
    exact List.get_mem _ _
  weight_le i := by
    apply s.weight_le
    rw [← coe_primeKummerSpectralList s.eigenvalues, Multiset.mem_coe]
    exact List.get_mem _ _
  trace_eq q := by
    rw [s.trace_eq q]
    congr 1
    let l := primeKummerSpectralList s.eigenvalues
    have hlen : l.length = R.toFinset.card - 1 := by
      exact (length_primeKummerSpectralList s.eigenvalues).trans s.card_eq
    let e : Fin (R.toFinset.card - 1) ≃ Fin l.length :=
      (Fin.castOrderIso hlen.symm).toEquiv
    calc
      (s.eigenvalues.map fun a => a ^ (q + 1)).sum =
          ((↑l : Multiset ℂ).map fun a => a ^ (q + 1)).sum := by
        rw [coe_primeKummerSpectralList]
      _ = (List.map (fun a => a ^ (q + 1)) l).sum := by
        rw [Multiset.map_coe, Multiset.sum_coe]
      _ = (List.ofFn (fun j : Fin l.length =>
          l.get j ^ (q + 1))).sum := by
        congr 1
        calc
          List.map (fun a => a ^ (q + 1)) l =
              List.map (fun a => a ^ (q + 1)) (List.ofFn l.get) := by
            rw [List.ofFn_get]
          _ = List.ofFn (fun j : Fin l.length =>
              l.get j ^ (q + 1)) := by
            rw [List.map_ofFn]
            rfl
      _ = ∑ j : Fin l.length, l.get j ^ (q + 1) :=
        List.sum_ofFn
      _ = ∑ i : Fin (R.toFinset.card - 1),
          primeKummerRootMultisetSpectrumEigenvalue s i ^ (q + 1) := by
        symm
        simpa [primeKummerRootMultisetSpectrumEigenvalue, l, e] using
          (Equiv.sum_comp e (fun j : Fin l.length => l.get j ^ (q + 1)))

theorem PrimeKummerExplicitRootMultisetSpectrum.extension_norm_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerExplicitRootMultisetSpectrum p χ R) (q : ℕ) :
    ‖primeRootMultisetExtensionCorrelation p χ R q‖ ≤
      ((R.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p ^ (q + 1) :=
  s.toEigenvalues.extension_norm_le q

theorem nonempty_primeKummerExplicitRootMultisetEigenvalues_iff_spectrum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    Nonempty (PrimeKummerExplicitRootMultisetEigenvalues p χ R) ↔
      Nonempty (PrimeKummerExplicitRootMultisetSpectrum p χ R) := by
  constructor
  · exact fun h => h.map
      PrimeKummerExplicitRootMultisetEigenvalues.toSpectrum
  · exact fun h => h.map
      PrimeKummerExplicitRootMultisetSpectrum.toEigenvalues

def TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        Nonempty (PrimeKummerExplicitRootMultisetSpectrum p χ R)

theorem taoPrimeKummerExplicitRootMultisetEigenvaluesFourRootsOrMore_iff_spectrum :
    TaoPrimeKummerExplicitRootMultisetEigenvaluesFourRootsOrMore ↔
      TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact nonempty_primeKummerExplicitRootMultisetEigenvalues_iff_spectrum.mp
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact nonempty_primeKummerExplicitRootMultisetEigenvalues_iff_spectrum.mpr
      (h p χ R hχ hzero hone hcard hreduced)

def TaoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum : Prop :=
  TaoPrimePowerLegendreEigenpair ∧
    TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore

theorem taoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues_iff_spectrum :
    TaoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues ↔
      TaoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum := by
  rw [TaoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues,
    TaoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum,
    taoPrimeKummerExplicitRootMultisetEigenvaluesFourRootsOrMore_iff_spectrum]

theorem TaoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum.toFull
    (h : TaoPrimeKummerExplicitEigenpairOrRootMultisetSpectrum) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues.toFull
    (taoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues_iff_spectrum.mpr h)

end
end Tao2026

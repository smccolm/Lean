import RiemannZeta.GuthMaynard.KloostermanPolynomialL
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PowerSeries.Basic

open Polynomial Classical
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

theorem harcosEtaPolynomial_multiset_prod
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (s : Multiset ((ZMod p)[X]))
    (hs : ∀ k ∈ s, k.Monic) :
    harcosEtaPolynomial p a b s.prod =
      (s.map (harcosEtaPolynomial p a b)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [harcosEtaPolynomial]
  | @cons k s ih =>
      have hsprod : s.prod.Monic := by
        simpa using monic_multiset_prod_of_monic s id
          (fun q hq ↦ hs q (Multiset.mem_cons_of_mem hq))
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        harcosEtaPolynomial_mul_of_monic p a b k s.prod
          (hs k (by simp)) hsprod,
        ih (fun q hq ↦ hs q (Multiset.mem_cons_of_mem hq))]

theorem harcosEtaPolynomial_eq_normalizedFactors_product
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (k : (ZMod p)[X]) (hk : k.Monic) :
    harcosEtaPolynomial p a b k =
      ((UniqueFactorizationMonoid.normalizedFactors k).map
        (harcosEtaPolynomial p a b)).prod := by
  have hk0 : k ≠ 0 := hk.ne_zero
  have hmonic : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors k,
      q.Monic := by
    intro q hq
    exact (Polynomial.mem_normalizedFactors_iff hk0).mp hq |>.2.1
  have hprod : (UniqueFactorizationMonoid.normalizedFactors k).prod = k := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hk0,
      hk.normalize_eq_self]
  calc
    harcosEtaPolynomial p a b k =
        harcosEtaPolynomial p a b
          (UniqueFactorizationMonoid.normalizedFactors k).prod := by rw [hprod]
    _ = ((UniqueFactorizationMonoid.normalizedFactors k).map
          (harcosEtaPolynomial p a b)).prod :=
      harcosEtaPolynomial_multiset_prod p a b _ hmonic

theorem harcosNormalizedFactors_irreducible_monic
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (k : (ZMod p)[X]) (hk : k.Monic)
    (q : (ZMod p)[X])
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors k) :
    Irreducible q ∧ q.Monic := by
  have h := (Polynomial.mem_normalizedFactors_iff hk.ne_zero).mp hq
  exact ⟨h.1, h.2.1⟩

theorem harcosNormalizedFactors_degree_sum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (k : (ZMod p)[X]) (hk : k.Monic) :
    ((UniqueFactorizationMonoid.normalizedFactors k).map
      Polynomial.natDegree).sum = k.natDegree := by
  have hmonic : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors k,
      q.Monic := by
    intro q hq
    exact (harcosNormalizedFactors_irreducible_monic p k hk q hq).2
  have hprod : (UniqueFactorizationMonoid.normalizedFactors k).prod = k := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hk.ne_zero,
      hk.normalize_eq_self]
  calc
    ((UniqueFactorizationMonoid.normalizedFactors k).map
        Polynomial.natDegree).sum =
        (UniqueFactorizationMonoid.normalizedFactors k).prod.natDegree :=
      (natDegree_multiset_prod_of_monic _ hmonic).symm
    _ = k.natDegree := congrArg Polynomial.natDegree hprod

/-- The `harcosLSeries` definition used by the source-facing construction in `KloostermanEulerProduct`. -/
noncomputable def harcosLSeries
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) : PowerSeries ℂ :=
  PowerSeries.mk (fun d ↦ harcosEtaDegreeSum p d a b)

/-- The `harcosFactorizedLSeries` definition used by the source-facing construction in `KloostermanEulerProduct`. -/
noncomputable def harcosFactorizedLSeries
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) : PowerSeries ℂ :=
  PowerSeries.mk (fun d ↦
    ∑ v : Fin d → ZMod p,
      ((UniqueFactorizationMonoid.normalizedFactors
          (monicPolynomialOfCoeffs p d v)).map
        (harcosEtaPolynomial p a b)).prod)

/-- Harcos equation (9), coefficientwise at its factorization stage: every monic
polynomial contributing to the finite-field `L`-series is replaced by its unique
multiset of monic irreducible factors, and eta is the product of their local weights. -/
theorem harcosEquationNine_factorization
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) :
    harcosLSeries p a b = harcosFactorizedLSeries p a b := by
  ext d
  simp only [harcosLSeries, harcosFactorizedLSeries, PowerSeries.coeff_mk]
  unfold harcosEtaDegreeSum
  apply Finset.sum_congr rfl
  intro v _hv
  exact harcosEtaPolynomial_eq_normalizedFactors_product p a b _
    (by
      rw [Polynomial.Monic, leadingCoeff,
        natDegree_monicPolynomialOfCoeffs,
        coeff_monicPolynomialOfCoeffs_self])

end RiemannZeta.GuthMaynard

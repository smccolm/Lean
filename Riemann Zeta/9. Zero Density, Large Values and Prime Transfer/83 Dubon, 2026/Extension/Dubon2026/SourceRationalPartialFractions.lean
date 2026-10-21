import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

/-! DUB-17/18 -> regular differential dimension -> global residue identity
-> rational-function spanning. The pinned partial-fraction theorem decomposes
every rational function into polynomial powers and irreducible principal parts.
Selected proof adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed. No geometric
or differential hypotheses enter this algebraic spanning statement.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial UniqueFactorizationMonoid
variable (K : Type*) [Field K]

/-- Polynomial powers of the actual rational-function coordinate. -/
def P1PolynomialGenerators : Set (RatFunc K) := Set.range fun n : ℕ => RatFunc.X ^ n

/-- Reduced principal fractions at monic irreducible polynomials. -/
def P1PrincipalPartGenerators : Set (RatFunc K) :=
  {f | ∃ (p c : K[X]) (m : ℕ), p.Monic ∧ Irreducible p ∧ c.degree < p.degree ∧ 1 ≤ m ∧
    f = algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m}

/-- Polynomial and proper principal fractions used in the spanning theorem. -/
def P1PartialFractionGenerators : Set (RatFunc K) :=
  P1PolynomialGenerators K ∪ P1PrincipalPartGenerators K

variable {K}

theorem gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PolynomialGenerators K) := by

  rw [← Polynomial.sum_C_mul_X_pow_eq q, Polynomial.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    ← RatFunc.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_monic_irreducible_factorization {d : K[X]} (hd : d.Monic) :
    ∃ (s : Finset K[X]) (n : K[X] → ℕ),
      (∀ p ∈ s, p.Monic) ∧ (∀ p ∈ s, Irreducible p) ∧
      (Set.Pairwise (s : Set K[X]) fun i j => IsCoprime i j) ∧
      d = ∏ p ∈ s, p ^ n p := by
  classical
  refine ⟨(normalizedFactors d).toFinset,
    fun p => (normalizedFactors d).count p, ?_, ?_, ?_, ?_⟩
  ·
    intro p hp
    exact ((Polynomial.mem_normalizedFactors_iff hd.ne_zero).mp
      (Multiset.mem_toFinset.mp hp)).2.1
  ·
    intro p hp
    exact irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
  ·

    intro p hp q hq hne
    have hp' := Multiset.mem_toFinset.mp hp
    have hq' := Multiset.mem_toFinset.mp hq
    rw [(irreducible_of_normalized_factor p hp').coprime_iff_not_dvd]
    exact fun hdvd => hne (normalizedFactors_eq_of_dvd d p hp' q hq' hdvd)
  ·

    calc d = (normalizedFactors d).prod := by
            rw [prod_normalizedFactors_eq hd.ne_zero, hd.normalize_eq_self]
      _ = ∏ p ∈ (normalizedFactors d).toFinset, p ^ (normalizedFactors d).count p :=
            Finset.prod_multiset_count _

theorem algebraMap_mem_span_P1PartialFractionGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PartialFractionGenerators K) :=
  Submodule.span_mono Set.subset_union_left
    (gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators q)

theorem div_pow_mem_span_P1PartialFractionGenerators
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) {m : ℕ} (hm : 1 ≤ m) :
    algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
      ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  exact Submodule.subset_span (Or.inr ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩)

theorem ratFunc_mem_span_P1PartialFractionGenerators (f : RatFunc K) :
    f ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  classical

  have hdenmon : f.denom.Monic := RatFunc.monic_denom f

  obtain ⟨s, n, hmon, hirr, hcop, hdfac⟩ :=
    exists_monic_irreducible_factorization hdenmon

  have hginv : ∀ p ∈ s,
      (algebraMap K[X] (RatFunc K) p)⁻¹ * algebraMap K[X] (RatFunc K) p = 1 :=
    fun p hp => inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (hmon p hp).ne_zero)

  obtain ⟨q, r, hr, hpfrac⟩ :=
    Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
      (K := RatFunc K) f.num hmon hcop n hginv

  have hLHS : algebraMap K[X] (RatFunc K) f.num *
      ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p = f := by
    have hprod : ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p
        = (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := by
      rw [hdfac, map_prod]
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p _ => by rw [map_pow, inv_pow]
    rw [hprod, ← div_eq_mul_inv, RatFunc.num_div_denom]
  rw [← hLHS, hpfrac]

  refine Submodule.add_mem _ (algebraMap_mem_span_P1PartialFractionGenerators q) ?_
  refine Submodule.sum_mem _ fun p hp => ?_
  refine Submodule.sum_mem _ fun j _ => ?_

  rw [inv_pow, ← div_eq_mul_inv]
  exact div_pow_mem_span_P1PartialFractionGenerators (hmon p hp) (hirr p hp)
    (hr p hp j) j.succ_pos

theorem p1PartialFractionSpan_eq_top :
    Submodule.span K (P1PartialFractionGenerators K) = ⊤ :=
  Submodule.eq_top_iff'.mpr ratFunc_mem_span_P1PartialFractionGenerators

end
end Dubon2026.SourceCurve

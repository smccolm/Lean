import Tao2026.BurgessWeilPrimeKummerLiteralWeilOnly
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Kummer irreducibility from root multiplicities

Norms of roots of irreducible factors give rational-function power relations.
Clearing denominators makes these divisibility conditions on every root
multiplicity. Coprimality of their gcd forces full factor degree, over every
extension of the coefficient field.
-/

namespace Tao2026
open Polynomial
noncomputable section

theorem polynomial_X_pow_sub_C_irreducible_of_power_relation_degree_dvd
    {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) (a : K)
    (hpower : ∀ b : K, ∀ d : ℕ, b ^ n = a ^ d → n ∣ d) :
    Irreducible (X ^ n - C a) := by
  have hunit : ¬ IsUnit (X ^ n - C a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hn, Nat.cast_eq_zero]
    exact hn.ne'
  obtain ⟨g, hg, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor hunit
    (X_pow_sub_C_ne_zero hn a)
  have key : (Algebra.norm K (AdjoinRoot.root g)) ^ n = a ^ g.natDegree := by
    have hroot := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hdiv (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at hroot
    rw [← map_pow, hroot, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap,
      (AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim hg.ne_zero]
  have hdeg : g.natDegree = n := by
    apply le_antisymm
    · exact (natDegree_le_of_dvd hdiv (X_pow_sub_C_ne_zero hn a)).trans_eq
        natDegree_X_pow_sub_C
    · exact Nat.le_of_dvd hg.natDegree_pos (hpower _ _ key)
  exact (associated_of_dvd_of_natDegree_le hdiv (X_pow_sub_C_ne_zero hn a)
    (hdeg.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg

theorem polynomial_rootMultiplicity_pow
    {K : Type*} [Field K] (P : K[X]) (r : K) (n : ℕ) :
    (P ^ n).rootMultiplicity r = n * P.rootMultiplicity r := by
  classical
  simp only [← count_roots, roots_pow, Multiset.count_nsmul]

theorem ratFunc_power_relation_dvd_rootMultiplicity
    {K : Type*} [Field K] (P : K[X]) (hP : P ≠ 0)
    (n d : ℕ) (b : RatFunc K)
    (heq : b ^ n = (algebraMap K[X] (RatFunc K) P) ^ d) (r : K) :
    n ∣ d * P.rootMultiplicity r := by
  have hpoly : b.num ^ n = P ^ d * b.denom ^ n := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    simp only [map_mul, map_pow]
    rw [← heq, ← mul_pow]
    congr 1
    exact (div_eq_iff (RatFunc.algebraMap_ne_zero b.denom_ne_zero)).1
      (RatFunc.num_div_denom b)
  have hmult := congrArg (fun Q : K[X] => Q.rootMultiplicity r) hpoly
  change (b.num ^ n).rootMultiplicity r = (P ^ d * b.denom ^ n).rootMultiplicity r at hmult
  rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero d hP)
    (pow_ne_zero n b.denom_ne_zero)), polynomial_rootMultiplicity_pow,
    polynomial_rootMultiplicity_pow, polynomial_rootMultiplicity_pow] at hmult
  have hdiv : n ∣ d * P.rootMultiplicity r + n * b.denom.rootMultiplicity r :=
    hmult ▸ dvd_mul_right n _
  exact (Nat.dvd_add_iff_left (dvd_mul_right n _)).2 hdiv

theorem polynomial_kummer_irreducible_of_coprime_rootMultiplicity_gcd_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (P : K[X]) (hP : P ≠ 0) (n : ℕ) (hn : 0 < n)
    (S : Finset K) (hcop : n.Coprime (S.gcd fun r => P.rootMultiplicity r)) :
    Irreducible (X ^ n - C (algebraMap L[X] (RatFunc L) (P.map f))) := by
  classical
  apply polynomial_X_pow_sub_C_irreducible_of_power_relation_degree_dvd n hn
  intro b d heq
  have hdiv : n ∣ S.gcd (fun r => d * P.rootMultiplicity r) := by
    apply Finset.dvd_gcd
    intro r _
    rw [eq_rootMultiplicity_map f.injective]
    exact ratFunc_power_relation_dvd_rootMultiplicity (P.map f)
      ((Polynomial.map_ne_zero_iff f.injective).2 hP) n d b heq (f r)
  rw [Finset.gcd_mul_left, normalize_eq] at hdiv
  exact hcop.dvd_of_dvd_mul_right hdiv

theorem polynomial_kummer_irreducible_of_coprime_rootMultiplicity_gcd
    {K : Type*} [Field K] (P : K[X]) (hP : P ≠ 0) (n : ℕ) (hn : 0 < n)
    (S : Finset K) (hcop : n.Coprime (S.gcd fun r => P.rootMultiplicity r)) :
    Irreducible (X ^ n - C (algebraMap K[X] (RatFunc K) P)) := by
  apply polynomial_X_pow_sub_C_irreducible_of_power_relation_degree_dvd n hn
  intro b d heq
  have hdiv : n ∣ S.gcd (fun r => d * P.rootMultiplicity r) :=
    Finset.dvd_gcd (fun r _ => ratFunc_power_relation_dvd_rootMultiplicity P hP n d b heq r)
  rw [Finset.gcd_mul_left, normalize_eq] at hdiv
  exact hcop.dvd_of_dvd_mul_right hdiv

end
end Tao2026

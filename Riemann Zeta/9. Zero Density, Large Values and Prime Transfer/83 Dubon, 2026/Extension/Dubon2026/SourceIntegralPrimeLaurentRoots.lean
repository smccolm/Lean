import Dubon2026.SourceIntegralPrimeConjugateProduct
import Dubon2026.SourceResiduePrimePolynomialRoots
import Mathlib.FieldTheory.Separable

/-! Reuse the already proved distinct Laurent roots for the exact integral
modular polynomial. Monicity and the original rational root identify the
previous adjacent relation with this polynomial. This supplies the separability
input for generic-fiber injectivity of the actual cyclic-root map, avoiding a
general elliptic-endomorphism classification on the DUB-17/18 inertia chain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial PrimeDegreeAux
noncomputable section

/-- The exact integral modular polynomial satisfies both adjacent Laurent relations in every characteristic. -/
theorem modularPolynomial_prime_adjacent_relations (p : ℕ) [Fact p.Prime]
    (K : Type*) [CommRing K] (a : ℕ) [NeZero a] :
    (relationAtSeed (modularPolynomial p) (qExpand K a (jqModC K))).eval
        (qExpand K (a * p) (jqModC K)) = 0 ∧
      (relationAtSeed (modularPolynomial p) (qExpand K (a * p) (jqModC K))).eval
        (qExpand K a (jqModC K)) = 0 := by
  obtain ⟨P, hm, hd, hrel⟩ := exists_prime_adjacent_relations p
  have h0 := (hrel 1).1
  simp only [qExpand_one_apply, one_mul, relationAtSeed, eval_map] at h0
  have heval : eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq = evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  rw [heval] at h0
  have he : P = modularPolynomial p :=
    eq_modularPolynomial_of_monic_root_degree p P hm
      h0
      (by rw [hd, ← modularPolynomial_natDegree, modularPolynomial_prime_natDegree])
  constructor
  · simpa only [he] using original_pair_j_relation_specializes K P a (a * p) (hrel a).1
  · simpa only [he] using original_pair_j_relation_specializes K P (a * p) a (hrel a).2

/-- The exact prime polynomial has the complete original multiset of distinct Laurent conjugates. -/
theorem modularPolynomial_prime_laurent_roots
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    (relationAtSeed (modularPolynomial p) (qExpand K p (jqModC K))).roots =
      TS K (p * p) 1 ::ₘ (Multiset.range p).map (fun b => TS K 1 (ζ ^ b)) := by
  apply residue_prime_polynomial_roots K p ζ hζ _
    (modularPolynomial_monic p) (modularPolynomial_prime_natDegree p)
  · exact (modularPolynomial_prime_adjacent_relations p K p).1
  · simpa only [one_mul, qExpand_one_apply] using
      (modularPolynomial_prime_adjacent_relations p K 1).2

/-- The exact prime Laurent specialization splits over the original Laurent field. -/
theorem modularPolynomial_prime_laurent_splits
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    (relationAtSeed (modularPolynomial p) (qExpand K p (jqModC K))).Splits := by
  rw [splits_iff_card_roots, modularPolynomial_prime_laurent_roots K p ζ hζ,
    Multiset.card_cons, Multiset.card_map, Multiset.card_range]
  exact (((modularPolynomial_monic p).natDegree_map _).trans
    (modularPolynomial_prime_natDegree p)).symm

/-- Distinctness of the actual Laurent conjugates proves separability of the exact polynomial. -/
theorem modularPolynomial_prime_laurent_separable
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    (relationAtSeed (modularPolynomial p) (qExpand K p (jqModC K))).Separable := by
  apply (nodup_roots_iff_of_splits ((modularPolynomial_monic p).map _).ne_zero
    (modularPolynomial_prime_laurent_splits K p ζ hζ)).mp
  change (relationAtSeed (modularPolynomial p) (qExpand K p (jqModC K))).roots.Nodup
  rw [modularPolynomial_prime_laurent_roots K p ζ hζ]
  exact roots_phiProd_conj_nodup p ζ hζ

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate

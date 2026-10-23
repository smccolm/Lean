import Dubon2026.SourceResidueRelationDegreeBounds
import Dubon2026.SourceResiduePrimePolynomialRoots

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> reverse expansion tower. A field inside the p-expansion
range fixes the p distinct twists of j. The actual prime relation gives an
upper degree p+1; when j(q^(p²)) is in that field its known linear factor
reduces the upper bound to p. This is the degree input to the prime-power
tower argument, valid in residue characteristic without rational cyclotomic
coefficient automorphisms. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_relfinrank_fullC_mul_prime_pow, eFullDegree section. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem residue_reverse_prime_integral
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (p : ℕ) [Fact p.Prime] (hp : qExpand K p (jqModC K) ∈ F) :
    IsIntegral F (jqModC K) := by
  obtain ⟨P, hm, _, hrel⟩ := exists_prime_adjacent_relations_coeff p
  apply integral_of_relationAtSeed_root F P hm hp
  simpa only [one_mul, qExpand_one_apply] using (hrel K 1).2

theorem residue_reverse_prime_degree_le
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (p : ℕ) [Fact p.Prime] (hp : qExpand K p (jqModC K) ∈ F) :
    (minpoly F (jqModC K)).natDegree ≤ p + 1 := by
  obtain ⟨P, hm, hd, hrel⟩ := exists_prime_adjacent_relations_coeff p
  rw [← hd]
  apply minpoly_degree_le_relationAtSeed F P hm hp
  simpa only [one_mul, qExpand_one_apply] using (hrel K 1).2

theorem residue_reverse_prime_degree_le_of_square_mem
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (p : ℕ) [Fact p.Prime] (hp : qExpand K p (jqModC K) ∈ F)
    (hpp : qExpand K (p * p) (jqModC K) ∈ F) :
    (minpoly F (jqModC K)).natDegree ≤ p := by
  obtain ⟨P, hm, hd, hrel⟩ := exists_prime_adjacent_relations_coeff p
  have hr : (relationAtSeed P (qExpand K p (jqModC K))).eval (jqModC K) = 0 := by
    simpa only [one_mul, qExpand_one_apply] using (hrel K 1).2
  have hne : jqModC K ≠ qExpand K (p * p) (jqModC K) := by
    intro he
    have ht : TS K 1 1 = TS K (p * p) 1 := by
      simpa only [TS, qExpand_one_apply, qTwist_one_apply] using he
    have h := (TS_injective ht).1
    have h2 := Nat.Prime.two_le (Fact.out : p.Prime)
    nlinarith
  have h := minpoly_degree_lt_relation_of_known_root F P hm hp hpp (hrel K p).1 hr hne
  omega

theorem residue_reverse_prime_degree_ge
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (hF : ∀ x ∈ F, x ∈ (qExpand K p).range) (hi : IsIntegral F (jqModC K)) :
    p ≤ (minpoly F (jqModC K)).natDegree := by
  classical
  let Q := (minpoly F (jqModC K)).map (algebraMap F (LaurentSeries K))
  have hQm : Q.Monic := (minpoly.monic hi).map _
  have hζp := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hroot (b : ℕ) : Q.eval (TS K 1 (ζ ^ b)) = 0 := by
    have hpow : (ζ ^ b) ^ p = 1 := by
      rw [← pow_mul, Nat.mul_comm b p, pow_mul, hζp, one_pow]
    have hfix : (qTwist (ζ ^ b)).comp (algebraMap F (LaurentSeries K)) =
        algebraMap F (LaurentSeries K) := by
      refine RingHom.ext fun x => ?_
      obtain ⟨y, hy⟩ := hF x x.2
      change qTwist (ζ ^ b) (x : LaurentSeries K) = x
      rw [← hy]
      exact qTwist_qExpand_of_pow_eq_one p (ζ ^ b) hpow y
    have h0 := minpoly.aeval F (jqModC K)
    rw [Polynomial.aeval_def] at h0
    have h := Polynomial.hom_eval₂ (minpoly F (jqModC K))
      (algebraMap F (LaurentSeries K)) (qTwist (ζ ^ b)) (jqModC K)
    rw [hfix, h0, map_zero] at h
    simpa only [Q, Polynomial.eval_map, TS, qExpand_one_apply] using h.symm
  have hnd := (Multiset.nodup_cons.mp (roots_phiProd_conj_nodup p ζ hζ)).2
  have hle : (Multiset.range p).map (fun b => TS K 1 (ζ ^ b)) ≤ Q.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hQm.ne_zero).mpr (hroot b)
  have hcard := (Multiset.card_le_card hle).trans (Polynomial.card_roots' Q)
  simpa only [Multiset.card_map, Multiset.card_range,
    Q, (minpoly.monic hi).natDegree_map] using hcard

theorem residue_reverse_prime_finrank_eq
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (hF : ∀ x ∈ F, x ∈ (qExpand K p).range)
    (hp : qExpand K p (jqModC K) ∈ F)
    (hpp : qExpand K (p * p) (jqModC K) ∈ F) :
    Module.finrank F (IntermediateField.adjoin F
      ({jqModC K} : Set (LaurentSeries K))) = p := by
  have hi := residue_reverse_prime_integral F p hp
  rw [IntermediateField.adjoin.finrank hi]
  exact le_antisymm (residue_reverse_prime_degree_le_of_square_mem F p hp hpp)
    (residue_reverse_prime_degree_ge F p ζ hζ hF hi)

end
end Dubon2026.SourceFunctionField

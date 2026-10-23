import Dubon2026.SourceModularRelationsInResidueCharacteristic
import Dubon2026.SourcePrimeAdjacentRelations

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree. The same proved integral prime polynomial supplies
both adjacent j relations in every coefficient characteristic. Specializing
the actual integral series preserves its degree p+1 and monicity. This avoids
a new cyclotomic lifting or modular-polynomial construction in residue fields. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem coeffMap_pair_j_relation {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Polynomial (Polynomial ℤ))
    (a b : ℕ) [NeZero a] [NeZero b] :
    coeffMap f ((relationAtSeed P (qExpand R a (jqModC R))).eval
      (qExpand R b (jqModC R))) =
      (relationAtSeed P (qExpand S a (jqModC S))).eval (qExpand S b (jqModC S)) := by
  have hj (n : ℕ) [NeZero n] :
      coeffMap f (qExpand R n (jqModC R)) = qExpand S n (jqModC S) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC f
  rw [← hj a, ← hj b,
    ← relationAtSeed_map P (qExpand R a (jqModC R)) (coeffMap f),
    Polynomial.eval_map_apply]

theorem original_pair_j_relation_specializes (K : Type*) [CommRing K]
    (P : Polynomial (Polynomial ℤ)) (a b : ℕ) [NeZero a] [NeZero b]
    (hQ : (relationAtSeed P (qExpand ℚ a jq)).eval (qExpand ℚ b jq) = 0) :
    (relationAtSeed P (qExpand K a (jqModC K))).eval (qExpand K b (jqModC K)) = 0 := by
  have hZ : (relationAtSeed P (qExpand ℤ a (jqModC ℤ))).eval
      (qExpand ℤ b (jqModC ℤ)) = 0 := by
    have hmap : coeffMap (Int.castRingHom ℚ)
        ((relationAtSeed P (qExpand ℤ a (jqModC ℤ))).eval
          (qExpand ℤ b (jqModC ℤ))) = 0 := by
      rw [coeffMap_pair_j_relation, jqModC_rat]
      exact hQ
    ext n
    have h := congrArg (fun x : LaurentSeries ℚ => x.coeff n) hmap
    simpa using h
  rw [← coeffMap_pair_j_relation (Int.castRingHom K) P a b, hZ, map_zero]

theorem exists_prime_adjacent_relations_coeff (p : ℕ) [Fact p.Prime] :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = p + 1 ∧
      ∀ (K : Type*) [CommRing K] (a : ℕ) [NeZero a],
        (relationAtSeed P (qExpand K a (jqModC K))).eval
          (qExpand K (a * p) (jqModC K)) = 0 ∧
        (relationAtSeed P (qExpand K (a * p) (jqModC K))).eval
          (qExpand K a (jqModC K)) = 0 := by
  obtain ⟨P, hm, hd, hrel⟩ := exists_prime_adjacent_relations p
  exact ⟨P, hm, hd, fun K _ a _ =>
    ⟨original_pair_j_relation_specializes K P a (a * p) (hrel a).1,
      original_pair_j_relation_specializes K P (a * p) a (hrel a).2⟩⟩

end
end Dubon2026.SourceFunctionField

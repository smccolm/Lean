import Dubon2026.SourceOriginalConjugateInduction

/-! DUB-17/18 -> numerical modular genus -> composite generation ->
descent of the preceding j-substitution from the unique common root of
its lower minimal polynomial and the actual prime relation. Native
minimal-polynomial divisibility, split roots and the degree-one criterion
give descent directly, avoiding a separate polynomial gcd construction.
The original-field application must supply the concrete pair of relations
and prove their common-root uniqueness from the indexed conjugate list.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem mem_range_of_unique_common_root_monic
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A B : Polynomial F) (hA : A.Monic)
    (hAs : (A.map (algebraMap F E)).Splits)
    (hAn : (A.map (algebraMap F E)).roots.Nodup)
    (x : E) (hxA : Polynomial.aeval x A = 0) (hxB : Polynomial.aeval x B = 0)
    (hu : ∀ y : E, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x) :
    x ∈ (algebraMap F E).range := by
  have hi : IsIntegral F x := ⟨A, hA, hxA⟩
  let P := (minpoly F x).map (algebraMap F E)
  have hm : P.Monic := (minpoly.monic hi).map _
  have hdA : P ∣ A.map (algebraMap F E) :=
    Polynomial.map_dvd _ (minpoly.dvd F x hxA)
  have hdB : P ∣ B.map (algebraMap F E) :=
    Polynomial.map_dvd _ (minpoly.dvd F x hxB)
  have hsplit : P.Splits := hAs.of_dvd (hA.map _).ne_zero hdA
  have hnodup : P.roots.Nodup :=
    Multiset.nodup_of_le (Polynomial.roots.le_of_dvd (hA.map _).ne_zero hdA) hAn
  have hle : P.roots ≤ {x} := by
    apply (Multiset.le_iff_subset hnodup).mpr
    intro y hy
    have hy0 := (Polynomial.mem_roots hm.ne_zero).mp hy
    have hyA := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdA hy0
    have hyB := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdB hy0
    rw [Polynomial.eval_map, ← Polynomial.aeval_def] at hyA hyB
    exact Multiset.mem_singleton.mpr (hu y hyA hyB)
  have hx : x ∈ P.roots := by
    apply (Polynomial.mem_roots hm.ne_zero).mpr
    change ((minpoly F x).map (algebraMap F E)).eval x = 0
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval F x
  have hc : P.roots.card = 1 := by
    have hupper := Multiset.card_le_card hle
    have hlower := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx⟩
    simpa using Nat.le_antisymm hupper hlower
  have hd : (minpoly F x).natDegree = 1 := by
    have h := hsplit.natDegree_eq_card_roots.trans hc
    simpa only [P, (minpoly.monic hi).natDegree_map] using h
  exact minpoly.natDegree_eq_one_iff.mp hd

end
end Dubon2026.SourceFunctionField

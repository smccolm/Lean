import Dubon2026.SourceExpandedJMinimalPolynomial

/-! DUB-17/18 -> numerical modular genus -> composite degree and generation
-> actual minimal-polynomial conjugates. Native multiset root divisibility
reduces the exact product identity to individual indexed-root obligations
and the lower-level induction's simple-field degree. Neither condition is
asserted here; the root construction and the degree/generation induction
must discharge them in the original-field consumer.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem expandedJMinpoly_qExpand (k A N : ℕ) [NeZero k] [NeZero A] [NeZero N] :
    (expandedJMinpoly K A N).map (qExpand K k) = expandedJMinpoly K (k * A) N := by
  rw [expandedJMinpoly, expandedJMinpoly, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply]
  change qExpand K k (coeffMap (algebraMap ℚ K) (qExpand ℚ A (x : LaurentSeries ℚ))) = _
  rw [← coeffMap_qExpand, qExpand_qExpand]
  rfl

theorem expandedJMinpoly_eq_slotProduct_of_roots_and_degree
    (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (hroots : ∀ s ∈ indices N,
      (expandedJMinpoly K N N).IsRoot (slotValue ζ s.1 s.2))
    (hdegree : Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮qExpand ℚ N jq⟯ =
      SourceLevelProjective.dedekindPsi N) :
    expandedJMinpoly K N N = slotProduct N ζ := by
  classical
  let T := (indices N).val.map (fun s => slotValue ζ s.1 s.2)
  have hn : T.Nodup := (indices N).nodup.map_on (slotValue_injOn_indices hζ)
  have hne : expandedJMinpoly K N N ≠ 0 := (expandedJMinpoly_monic K N N).ne_zero
  have hle : T ≤ (expandedJMinpoly K N N).roots := by
    apply (Multiset.le_iff_subset hn).mpr
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hne).mpr (hroots s hs)
  have hdvd : slotProduct N ζ ∣ expandedJMinpoly K N N := by
    have h := (T.prod_X_sub_C_dvd_iff_le_roots hne).mpr hle
    simpa only [T, Multiset.map_map, Function.comp_def, slotProduct,
      Finset.prod_eq_multiset_prod] using h
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (slotProduct_monic N ζ)
    (expandedJMinpoly_monic K N N) hdvd
  rw [expandedJMinpoly_natDegree, hdegree, slotProduct_natDegree N (NeZero.ne N)]

theorem expandedJMinpoly_top_slot_root (N : ℕ) [NeZero N] (ζ : Kˣ) :
    (expandedJMinpoly K N N).IsRoot (slotValue ζ N 0) := by
  rw [slotValue_eq, zero_mul, pow_zero]
  exact expandedJMinpoly_distinguished_root K N N

end
end Dubon2026.SourceFunctionField

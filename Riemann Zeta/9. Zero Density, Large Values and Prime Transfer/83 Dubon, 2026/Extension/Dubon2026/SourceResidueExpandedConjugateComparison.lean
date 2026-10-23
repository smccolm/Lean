import Dubon2026.SourceResidueExpandedMinimalPolynomial

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate product.
Native root divisibility reduces the actual expanded minimal-polynomial
identity to the indexed roots and degree supplied by the lower-level induction.
The already proved slot product, root distinctness and count work in every
coefficient characteristic. Adapted from local SourceExpandedJConjugateComparison. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residueExpandedJMinpoly_qExpand (k A N : ℕ) [NeZero k] [NeZero A] [NeZero N] :
    (residueExpandedJMinpoly K A N).map (qExpand K k) = residueExpandedJMinpoly K (k * A) N := by
  rw [residueExpandedJMinpoly, residueExpandedJMinpoly, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply]
  change qExpand K k (qExpand K A (x : LaurentSeries K)) = _
  rw [qExpand_qExpand]
  rfl

theorem residueExpandedJMinpoly_eq_slotProduct_of_roots_and_degree
    (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (hroots : ∀ s ∈ indices N,
      (residueExpandedJMinpoly K N N).IsRoot (slotValue ζ s.1 s.2))
    (hdegree : Module.finrank K⟮(jqModC K)⟯ K⟮(jqModC K)⟯⟮qExpand K N (jqModC K)⟯ =
      SourceLevelProjective.dedekindPsi N) :
    residueExpandedJMinpoly K N N = slotProduct N ζ := by
  classical
  let T := (indices N).val.map (fun s => slotValue ζ s.1 s.2)
  have hn : T.Nodup := (indices N).nodup.map_on (slotValue_injOn_indices hζ)
  have hne : residueExpandedJMinpoly K N N ≠ 0 := (residueExpandedJMinpoly_monic K N N).ne_zero
  have hle : T ≤ (residueExpandedJMinpoly K N N).roots := by
    apply (Multiset.le_iff_subset hn).mpr
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hne).mpr (hroots s hs)
  have hdvd : slotProduct N ζ ∣ residueExpandedJMinpoly K N N := by
    have h := (T.prod_X_sub_C_dvd_iff_le_roots hne).mpr hle
    simpa only [T, Multiset.map_map, Function.comp_def, slotProduct,
      Finset.prod_eq_multiset_prod] using h
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (slotProduct_monic N ζ)
    (residueExpandedJMinpoly_monic K N N) hdvd
  rw [residueExpandedJMinpoly_natDegree, hdegree, slotProduct_natDegree N (NeZero.ne N)]

theorem residueExpandedJMinpoly_top_slot_root (N : ℕ) [NeZero N] (ζ : Kˣ) :
    (residueExpandedJMinpoly K N N).IsRoot (slotValue ζ N 0) := by
  rw [slotValue_eq, zero_mul, pow_zero]
  exact residueExpandedJMinpoly_distinguished_root K N N

end
end Dubon2026.SourceFunctionField

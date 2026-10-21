import Dubon2026.SourceOriginalReducedPolynomial

/-! DUB-17/18 -> numerical modular genus -> composite degree ->
prime nonmembership over an arbitrary coprime base level. Every lower
conjugate supplies a range-preserving embedding. If j_p belonged to the
lower field, the actual prime relation would force the same image under
all these embeddings. Its bounded polynomial expression is therefore constant,
contradicting the already proved rational-j nonmembership.
Only the lower-level generation and conjugate-product identity remain
explicit; no current-level degree is used.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem prime_j_not_mem_original_coprime_of_conjugate_product
    (M p : ℕ) [NeZero M] [hp : Fact p.Prime] (hpM : ¬ p ∣ M)
    (η : Kˣ) (hη : IsPrimitiveRoot (η : K) M)
    (hgen : modularFunctionFieldFull M =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ M jq} : Set (LaurentSeries ℚ)))
    (hP : expandedJMinpoly K M M = slotProduct M η) :
    qExpand ℚ p jq ∉ modularFunctionFieldFull M := by
  classical
  intro hmem
  let S := (indices M).image (fun s => qExpand K p (slotValue η s.1 s.2))
  have hcard : S.card = dedekindPsi M := by
    dsimp only [S]
    rw [Finset.card_image_of_injOn, card_indices M (NeZero.ne M)]
    intro s hs t ht he
    exact slotValue_injOn_indices hη hs ht ((qExpand K p).injective he)
  have hdeg : (minpoly ℚ⟮jq⟯ (qExpand ℚ M jq)).natDegree = dedekindPsi M := by
    have h := congrArg Polynomial.natDegree hP
    rw [expandedJMinpoly, (minpoly.monic (original_j_substitution_isIntegral M)).natDegree_map,
      slotProduct_natDegree M (NeZero.ne M)] at h
    exact h
  obtain ⟨g, hgdeg, hg⟩ := original_member_reduced_polynomial M hgen (qExpand ℚ p jq) hmem
  have hgcard : g.natDegree < S.card := by rwa [hcard, ← hdeg]
  let φ : ℚ⟮jq⟯ →+* LaurentSeries K :=
    ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))
  have hval : ∀ y ∈ S, g.eval₂ φ y = TS K (M * p * p) 1 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    have hroot := expanded_minpoly_slot_root_of_identity p M η hP s hs
    have hroot' : (expandedJMinpoly K (M * p) M).IsRoot
        (qExpand K p (slotValue η s.1 s.2)) := by
      simpa only [Nat.mul_comm p M] using hroot
    obtain ⟨σ, hbase, hnew, hrange⟩ := original_conjugate_embedding_in_prime_expansion_range
      M p hgen _ hroot' ⟨slotValue η s.1 s.2, rfl⟩
    have hσj : σ ⟨jq, jq_mem_full M⟩ = TS K (M * p) 1 := by
      have h := hbase ⟨jq, IntermediateField.mem_adjoin_simple_self ℚ jq⟩ (jq_mem_full M)
      exact h.trans (coeffEmb_qExpand_jq_eq_TS (M * p))
    have himage := prime_j_image_of_coprime_expansion_range M p hpM
      (modularFunctionFieldFull M) (jq_mem_full M) hmem σ hσj (hrange ⟨_, hmem⟩)
    have h := original_polynomial_value_under_embedding M (M * p) σ hbase
      g (qExpand ℚ p jq) hmem hg
    rw [hnew] at h
    exact h.trans himage
  obtain ⟨z, hz⟩ := polynomial_value_mem_range_of_eval_eq_const φ g
    (TS K (M * p * p) 1) S hgcard hval
  have hx : coeffEmb K (qExpand ℚ (M * p) (qExpand ℚ p jq)) = TS K (M * p * p) 1 := by
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
  have he : (z : LaurentSeries ℚ) = qExpand ℚ p jq :=
    (((coeffEmb K).comp (qExpand ℚ (M * p))).injective (hz.trans hx.symm))
  apply prime_j_not_mem_original_one p
  rw [original_level_one_field_eq, ← he]
  exact z.2

end
end Dubon2026.SourceFunctionField

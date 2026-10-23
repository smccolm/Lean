import Dubon2026.SourceResidueReducedPolynomial
import Dubon2026.SourcePrimeJResidueNonmembership

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue degree -> coprime prime nonmembership. Adapt local SourceOriginalCoprimeNonmembership
to actual coefficient-field j series and divisor fields. Lower generation and
conjugate products are explicit induction inputs. Expansion-range preservation
forces each image of j_p to the distinguished branch; bounded polynomial
descent contradicts the already proved prime nonmembership in K(j).
The level and prime must remain nonzero in the coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem prime_j_not_mem_residue_coprime_of_conjugate_product
    (M p : ℕ) [NeZero M] [hp : Fact p.Prime] (hpM : ¬ p ∣ M) (hpK : (p : K) ≠ 0)
    (η : Kˣ) (hη : IsPrimitiveRoot (η : K) M)
    (hgen : modularFunctionFieldCoeff M K =
      IntermediateField.adjoin K ({(jqModC K), qExpand K M (jqModC K)} : Set (LaurentSeries K)))
    (hP : residueExpandedJMinpoly K M M = slotProduct M η) :
    qExpand K p (jqModC K) ∉ modularFunctionFieldCoeff M K := by
  classical
  intro hmem
  let S := (indices M).image (fun s => qExpand K p (slotValue η s.1 s.2))
  have hcard : S.card = dedekindPsi M := by
    dsimp only [S]
    rw [Finset.card_image_of_injOn, card_indices M (NeZero.ne M)]
    intro s hs t ht he
    exact slotValue_injOn_indices hη hs ht ((qExpand K p).injective he)
  have hdeg : (minpoly K⟮(jqModC K)⟯ (qExpand K M (jqModC K))).natDegree = dedekindPsi M := by
    have h := congrArg Polynomial.natDegree hP
    rw [residueExpandedJMinpoly, (minpoly.monic (residue_j_substitution_isIntegral K M)).natDegree_map,
      slotProduct_natDegree M (NeZero.ne M)] at h
    exact h
  obtain ⟨g, hgdeg, hg⟩ := residue_member_reduced_polynomial M hgen (qExpand K p (jqModC K)) hmem
  have hgcard : g.natDegree < S.card := by rwa [hcard, ← hdeg]
  let φ : K⟮(jqModC K)⟯ →+* LaurentSeries K :=
    ((qExpand K (M * p))).comp (algebraMap K⟮(jqModC K)⟯ (LaurentSeries K))
  have hval : ∀ y ∈ S, g.eval₂ φ y = TS K (M * p * p) 1 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    have hroot := residue_expanded_minpoly_slot_root_of_identity p M η hP s hs
    have hroot' : (residueExpandedJMinpoly K (M * p) M).IsRoot
        (qExpand K p (slotValue η s.1 s.2)) := by
      simpa only [Nat.mul_comm p M] using hroot
    obtain ⟨σ, hbase, hnew, hrange⟩ := residue_conjugate_embedding_in_prime_expansion_range
      M p hgen _ hroot' ⟨slotValue η s.1 s.2, rfl⟩
    have hσj : σ ⟨(jqModC K), jq_mem_coeff_field M K⟩ = TS K (M * p) 1 := by
      have h := hbase ⟨(jqModC K), IntermediateField.mem_adjoin_simple_self K (jqModC K)⟩ (jq_mem_coeff_field M K)
      exact h.trans (by rw [TS, qTwist_one_apply])
    have himage := residue_prime_j_image_of_coprime_expansion_range M p hpM hpK
      (modularFunctionFieldCoeff M K) (jq_mem_coeff_field M K) hmem σ hσj (hrange ⟨_, hmem⟩)
    have h := residue_polynomial_value_under_embedding M (M * p) σ hbase
      g (qExpand K p (jqModC K)) hmem hg
    rw [hnew] at h
    exact h.trans himage
  obtain ⟨z, hz⟩ := polynomial_value_mem_range_of_eval_eq_const φ g
    (TS K (M * p * p) 1) S hgcard hval
  have hx : (qExpand K (M * p) (qExpand K p (jqModC K))) = TS K (M * p * p) 1 := by
    simp only [qExpand_qExpand, TS, qTwist_one_apply]
  have he : (z : LaurentSeries K) = qExpand K p (jqModC K) :=
    (((qExpand K (M * p))).injective (hz.trans hx.symm))
  apply prime_j_not_mem_rational_j_away_characteristic p K hpK
  rw [← he]
  exact z.2

end
end Dubon2026.SourceFunctionField

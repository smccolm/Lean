import Dubon2026.SourceOriginalBaseChangedMinpoly

/-! DUB-17/18 -> numerical modular genus -> cusp classification -> actual
conjugate Laurent embeddings. The proved coefficient-extension identity
for the minimal polynomial and its exact conjugate product supply every
root. Native AdjoinRoot then constructs a coefficient-linear embedding of
the original field with the prescribed images of j and j_N. These are
the maps whose restricted valuations classify the places over infinity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_card_poles_jqModC_modularFunctionFieldFullC_eq_cuspCount.lean,
slotEmbedding; all degree and generation premises are supplied locally.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
open scoped IntermediateField
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem original_expanded_minpoly_over :
    (minpoly (DegreeTransport.K L jq) (coeffEmb L (qExpand ℚ N jq))).map
      ((qExpand L N).comp (algebraMap (DegreeTransport.K L jq) (LaurentSeries L))) =
        expandedJMinpoly L N N := by
  rw [original_minpoly_eq_map_over, Polynomial.map_map, expandedJMinpoly]
  congr 1
  apply RingHom.ext
  intro x
  exact (coeffMap_qExpand (algebraMap ℚ L) N (x : LaurentSeries ℚ)).symm

theorem original_slot_embedding [IsAlgClosed L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) N)
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    ∃ ι : modularFunctionFieldOver N L →ₐ[L] LaurentSeries L,
      ι (jOver N L) = TS L N 1 ∧ ι (jNOver N L) = slotValue ζ s.1 s.2 := by
  let B := DegreeTransport.K L jq
  let x := coeffEmb L (qExpand ℚ N jq)
  let S := IntermediateField.adjoin B ({x} : Set (LaurentSeries L))
  have hi : IsIntegral B x := original_j_substitution_isIntegral_over N L
  have hr : (minpoly B x).eval₂ ((qExpand L N).comp (algebraMap B (LaurentSeries L)))
      (slotValue ζ s.1 s.2) = 0 := by
    rw [← Polynomial.eval_map, original_expanded_minpoly_over]
    have h := expanded_minpoly_slot_root_of_identity 1 N ζ
      (expandedJMinpoly_eq_slotProduct N ζ hζ) s hs
    simpa only [one_mul, qExpand_one_apply] using h
  let A := AdjoinRoot.lift ((qExpand L N).comp (algebraMap B (LaurentSeries L)))
    (slotValue ζ s.1 s.2) hr
  let e := adjoinRootEquivAdjoin B hi
  let φ : S →+* LaurentSeries L := A.comp (e.symm : S →+* AdjoinRoot (minpoly B x))
  have hφalg : ∀ z : B, φ (algebraMap B S z) = qExpand L N z := by
    intro z
    change A (e.symm (algebraMap B S z)) = _
    rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
    rfl
  have hφgen : φ (AdjoinSimple.gen B x) = slotValue ζ s.1 s.2 := by
    change A (e.symm (AdjoinSimple.gen B x)) = _
    rw [adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.lift_root]
  let ι' : S.restrictScalars L →ₐ[L] LaurentSeries L :=
    { toRingHom := φ
      commutes' := fun c => by
        change φ (algebraMap B S (algebraMap L B c)) = _
        rw [hφalg]
        change qExpand L N (algebraMap L (LaurentSeries L) c) = _
        rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, qExpand_single, mul_zero] }
  let ι := ι'.comp (IntermediateField.inclusion (original_field_eq_simple_restrict_over N L).le)
  refine ⟨ι, ?_, hφgen⟩
  have h := hφalg ⟨coeffEmb L jq, IntermediateField.mem_adjoin_simple_self L _⟩
  change φ (algebraMap B S ⟨coeffEmb L jq, IntermediateField.mem_adjoin_simple_self L _⟩) = _
  rw [h]
  exact (coeffMap_qExpand (algebraMap ℚ L) N jq).symm.trans (coeffEmb_qExpand_jq_eq_TS N)

end
end Dubon2026.SourceFunctionField

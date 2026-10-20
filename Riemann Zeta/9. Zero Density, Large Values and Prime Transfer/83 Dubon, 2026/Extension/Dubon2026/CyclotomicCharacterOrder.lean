import Dubon2026.OriginalCyclotomicPrimeStage
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Exact orders in the original primitive-root character. This is the
finite cyclotomic input to BLGG Lemma 6.1.2 on DUB-17's potential-automorphy
chain, retaining the original adjoined field and original Galois action. -/

namespace Dubon2026
noncomputable section

/-- Restriction to the original adjoined primitive-root field preserves the actual cyclotomic character. -/
theorem primitiveRoot_character_restrict_originalStage
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (l : ℕ) [NeZero l] {z : Ω} (hz : IsPrimitiveRoot z l) (g : Gal(Ω/K)) :
    hz.autToPow K g = (originalPrimitiveRootStageRoot_isPrimitive K Ω hz).autToPow K
      (AlgEquiv.restrictNormalHom (originalPrimitiveRootStage K Ω hz) g) := by
  let F := originalPrimitiveRootStage K Ω hz
  let zF : F := originalPrimitiveRootStageRoot K Ω hz
  have hzF : IsPrimitiveRoot zF l := originalPrimitiveRootStageRoot_isPrimitive K Ω hz
  apply Units.ext
  apply ZMod.val_injective
  apply hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [hz.autToPow_spec K]
  have hroot := (hzF.autToPow_spec K (AlgEquiv.restrictNormalHom F g)).symm
  simpa only [AlgEquiv.restrictNormalHom_apply, map_pow] using
    congrArg (fun x : F => (x : Ω)) hroot

/-- A genuine Galois element has primitive-root character order equal to the degree of the original cyclotomic field. -/
theorem primitiveRoot_exists_character_order_eq_degree
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (l : ℕ) [Fact l.Prime] {z : Ω} (hz : IsPrimitiveRoot z l) :
    ∃ g : Gal(Ω/K), orderOf (hz.autToPow K g) =
      Module.finrank K (originalPrimitiveRootStage K Ω hz) := by
  let F := originalPrimitiveRootStage K Ω hz
  have hzF := originalPrimitiveRootStageRoot_isPrimitive K Ω hz
  letI : IsCyclic Gal(F/K) := isCyclic_of_injective (hzF.autToPow K) (hzF.autToPow_injective K)
  obtain ⟨gF, hgF⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(F/K))
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective Ω gF
  refine ⟨g, ?_⟩
  rw [primitiveRoot_character_restrict_originalStage K Ω l hz g, hg,
    orderOf_injective (hzF.autToPow K) (hzF.autToPow_injective K), hgF,
    IsGalois.card_aut_eq_finrank]

/-- The order of every actual primitive-root character value is bounded by the degree of its original adjoined field. -/
theorem primitiveRoot_character_order_le_degree
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (l : ℕ) [NeZero l] {z : Ω} (hz : IsPrimitiveRoot z l) (g : Gal(Ω/K)) :
    orderOf (hz.autToPow K g) ≤ Module.finrank K (originalPrimitiveRootStage K Ω hz) := by
  let F := originalPrimitiveRootStage K Ω hz
  have hzF := originalPrimitiveRootStageRoot_isPrimitive K Ω hz
  rw [primitiveRoot_character_restrict_originalStage K Ω l hz g,
    orderOf_injective (hzF.autToPow K) (hzF.autToPow_injective K),
    ← IsGalois.card_aut_eq_finrank]
  exact orderOf_le_card

end
end Dubon2026

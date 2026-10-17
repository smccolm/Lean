import Dubon2026.OriginalCharacterHomologyDescent

/-! # All original first-homology functionals arise from cocycles

This is the surjectivity half of the character pairing needed for
DUB-17's finite class/Ext duality. The functional extends from the
actual cycle submodule to the actual chain module; its values on single
chains then give the required character-valued cocycle.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]
variable (Q : Type) [AddCommGroup Q] [Module k Q] [Module.Injective k Q]
variable (M : Rep.{0} k G)

/-- Descended original character evaluation is linear in the cocycle. -/
def originalCharacterHomologyEvaluationLinear :
    groupCohomology.cocycles₁ (originalLinearCharacterRep Q M) →ₗ[k]
      (groupHomology M 1 →ₗ[k] Q) where
  toFun := originalCharacterHomologyEvaluation Q M
  map_add' c d := by
    apply LinearMap.ext
    intro x
    induction x using groupHomology.H1_induction_on with
    | h z =>
      change originalCharacterHomologyEvaluation Q M (c + d) (groupHomology.H1π M z) = _
      calc
        _ = originalCharacterChainEvaluation Q M (c + d).val z.val :=
          originalCharacterHomologyEvaluation_cycle Q M (c + d) z
        _ = originalCharacterChainEvaluation Q M c.val z.val +
            originalCharacterChainEvaluation Q M d.val z.val := by
          change Finsupp.lsum k (c.val + d.val) z.val = _
          exact congrArg (fun f : (G →₀ M) →ₗ[k] Q => f z.val)
            ((Finsupp.lsum k).map_add c.val d.val)
        _ = _ := congrArg₂ (· + ·)
          (originalCharacterHomologyEvaluation_cycle Q M c z).symm
          (originalCharacterHomologyEvaluation_cycle Q M d z).symm
  map_smul' r c := by
    apply LinearMap.ext
    intro x
    induction x using groupHomology.H1_induction_on with
    | h z =>
      change originalCharacterHomologyEvaluation Q M (r • c) (groupHomology.H1π M z) = _
      calc
        _ = originalCharacterChainEvaluation Q M (r • c).val z.val :=
          originalCharacterHomologyEvaluation_cycle Q M (r • c) z
        _ = r • originalCharacterChainEvaluation Q M c.val z.val := by
          change Finsupp.lsum k (r • c.val) z.val = _
          exact congrArg (fun f : (G →₀ M) →ₗ[k] Q => f z.val)
            ((Finsupp.lsum k).map_smul r c.val)
        _ = _ := congrArg (r • ·)
          (originalCharacterHomologyEvaluation_cycle Q M c z).symm

/-- Every functional on original first homology is evaluation against an actual character cocycle. -/
theorem originalCharacterHomologyEvaluation_surjective :
    Function.Surjective (originalCharacterHomologyEvaluationLinear Q M) := by
  intro χ
  obtain ⟨E, hE⟩ := Module.Injective.out (groupHomology.cycles₁ M).subtype
    Subtype.val_injective (χ ∘ₗ (groupHomology.H1π M).hom)
  let c : G → M →ₗ[k] Q := fun g => E ∘ₗ Finsupp.lsingle g
  have he : originalCharacterChainEvaluation Q M c = E := by
    apply Finsupp.lhom_ext
    intro g x
    rw [originalCharacterChainEvaluation_single]
    rfl
  have hc : c ∈ groupCohomology.cocycles₁ (originalLinearCharacterRep Q M) := by
    apply (originalCharacter_cocycle_iff_boundary_annihilation Q M c).mpr
    intro z
    rw [he]
    let b : groupHomology.cycles₁ M :=
      ⟨groupHomology.d₂₁ M z, groupHomology.d₂₁_apply_mem_cycles₁ z⟩
    have hb : groupHomology.H1π M b = 0 :=
      (groupHomology.H1π_eq_zero_iff b).mpr ⟨z, rfl⟩
    have hv := hE b
    change E (groupHomology.d₂₁ M z) = χ (groupHomology.H1π M b) at hv
    exact hv.trans (by rw [hb, map_zero])
  refine ⟨⟨c, hc⟩, ?_⟩
  apply LinearMap.ext
  intro x
  induction x using groupHomology.H1_induction_on with
  | h z =>
    change originalCharacterHomologyEvaluation Q M ⟨c, hc⟩ (groupHomology.H1π M z) = _
    rw [originalCharacterHomologyEvaluation_cycle, he]
    exact hE z

end
end Dubon2026

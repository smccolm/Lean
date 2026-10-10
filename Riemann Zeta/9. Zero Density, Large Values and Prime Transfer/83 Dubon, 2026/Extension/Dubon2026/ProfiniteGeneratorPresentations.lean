import Dubon2026.ProfiniteRepresentationExtension
import Mathlib.GroupTheory.Finiteness

/-! # Genuine profinite presentations on the original finite topological generators -/

namespace Dubon2026

noncomputable section

/-- The actual free group on the original finite generator set maps continuously from its genuine profinite completion to the original target. -/
def profiniteGeneratorPresentation (G : ProfiniteGrp) (S : Finset G) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup S)) →ₜ* G :=
  profiniteRepresentationExtension (FreeGroup.lift (fun s : S => s.val))

/-- Every original free generator maps to its exact original target element. -/
theorem profiniteGeneratorPresentation_generator (G : ProfiniteGrp) (S : Finset G) (s : S) :
    profiniteGeneratorPresentation G S
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup S)) (FreeGroup.of s)) = s.val := by
  rw [profiniteGeneratorPresentation, profiniteRepresentationExtension_eta, FreeGroup.lift_apply_of]

/-- Original topological generation makes the genuine profinite free-group presentation surjective onto the entire original group. -/
theorem profiniteGeneratorPresentation_surjective (G : ProfiniteGrp) (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) :
    Function.Surjective (profiniteGeneratorPresentation G S) := by
  let f := profiniteGeneratorPresentation G S
  have hclosed : IsClosed (f.toMonoidHom.range : Set G) :=
    (isCompact_range f.continuous_toFun).isClosed
  have hgen : Subgroup.closure (S : Set G) ≤ f.toMonoidHom.range := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    exact ⟨ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup S))
      (FreeGroup.of (⟨g, hg⟩ : S)), profiniteGeneratorPresentation_generator G S ⟨g, hg⟩⟩
  have hall := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [hS] at hall
  exact MonoidHom.range_eq_top.mp (eq_top_iff.mpr hall)

/-- All original presentation relations form the actual closed kernel of the genuine continuous free-group presentation. -/
theorem profiniteGeneratorPresentation_kernel_isClosed (G : ProfiniteGrp) (S : Finset G) :
    IsClosed ((profiniteGeneratorPresentation G S).toMonoidHom.ker :
      Set (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup S)))) :=
  isClosed_singleton.preimage (profiniteGeneratorPresentation G S).continuous_toFun

/-- The actual abstract free group on the original finite generator set is finitely generated. -/
theorem profiniteGeneratorPresentation_freeGroup_finiteGeneration
    (G : ProfiniteGrp) (S : Finset G) : Group.FG (FreeGroup S) := by
  infer_instance

end
end Dubon2026

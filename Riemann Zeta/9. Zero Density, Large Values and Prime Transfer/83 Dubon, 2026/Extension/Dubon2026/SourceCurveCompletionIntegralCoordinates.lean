import Dubon2026.SourceCurveCompletionIntegralBasis
import Dubon2026.SourceCurveLocalRetractionTrace

/-! The proved integral basis gives literal integral coordinates on each
completed extension. These coordinates will identify its local residue
commutator with the already proved matrix trace, the remaining local
extension step in DUB-17/18 residue/field-trace compatibility. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The completed extension retains the literal original constant-field action. -/
instance completionConstantsTower : IsScalarTower K (w.restrict F).adicCompletion w.adicCompletion :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K F (w.restrict F).adicCompletion,
      w.algebraMap_completionExtension, w.adicCompletionComap_algebraMap,
      ← IsScalarTower.algebraMap_apply K F E,
      ← IsScalarTower.algebraMap_apply K E w.adicCompletion]

/-- The actual completed field basis as coordinates over the original constants. -/
def completionBasisCoordinates (D : w.CompletionIntegralBasis (F := F)) :
    w.adicCompletion ≃ₗ[K]
      (Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion) →
        (w.restrict F).adicCompletion) :=
  D.basis.equivFun.restrictScalars K

/-- Each actual integral element has integral coordinates in the constructed basis. -/
def completionIntegralCoordinatesMap (D : w.CompletionIntegralBasis (F := F)) :
    w.completionPlace.integralFunctions →ₗ[K]
      (Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion) →
        (w.restrict F).completionPlace.integralFunctions) :=
  LinearMap.pi fun i =>
    ((LinearMap.proj i) ∘ₗ (w.completionBasisCoordinates D).toLinearMap ∘ₗ
      w.completionPlace.integralFunctions.subtype).codRestrict _
        (fun a => (D.mem_iff a).mp a.2 i)

/-- Integral coordinates give a bijection with the product of the actual base integral spaces. -/
theorem completionIntegralCoordinatesMap_bijective (D : w.CompletionIntegralBasis (F := F)) :
    Function.Bijective (w.completionIntegralCoordinatesMap D) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply (w.completionBasisCoordinates D).injective
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  · intro y
    let z := D.basis.equivFun.symm (fun i => (y i : (w.restrict F).adicCompletion))
    have hz : z ∈ w.adicCompletionIntegers := by
      apply (D.mem_iff z).mpr
      intro i
      have he : D.basis.repr z i = (y i : (w.restrict F).adicCompletion) :=
        congrFun (D.basis.equivFun.apply_symm_apply _) i
      rw [he]
      exact (y i).2
    refine ⟨⟨z, hz⟩, ?_⟩
    funext i
    apply Subtype.ext
    exact congrFun (D.basis.equivFun.apply_symm_apply _) i

/-- The constructed integral basis gives actual integral coordinate equivalences. -/
def completionIntegralCoordinates (D : w.CompletionIntegralBasis (F := F)) :
    w.completionPlace.integralFunctions ≃ₗ[K]
      (Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion) →
        (w.restrict F).completionPlace.integralFunctions) :=
  LinearEquiv.ofBijective (w.completionIntegralCoordinatesMap D)
    (w.completionIntegralCoordinatesMap_bijective D)

end Dubon2026.SourceCurve.Place

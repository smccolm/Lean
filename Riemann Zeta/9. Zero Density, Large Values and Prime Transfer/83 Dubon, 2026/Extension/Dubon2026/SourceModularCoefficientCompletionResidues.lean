import Dubon2026.SourceCurveCompletionResidueField
import Dubon2026.SourceCurveCompletionRetraction
import Dubon2026.SourceModularCoefficientLocalResidues

/-! The literal modular coefficient field and its actual completions have
the same rational residues and finite principal parts. The constructed
completed integral retraction extends the original projection, preparing
the finite-rank trace comparison required by DUB-17/18 global residues. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The actual modular completion has exactly the original constant residue field. -/
theorem coeff_completion_residue_algebraMap_bijective
    (v : Place K (modularFunctionFieldCoeff N K)) :
    Function.Bijective (algebraMap K v.completionPlace.ResidueField) :=
  ⟨(algebraMap K v.completionPlace.ResidueField).injective,
    v.completionPlace_residue_algebraMap_surjective
      (coeff_place_residue_algebraMap_bijective N K v).surjective⟩

omit [NeZero N] [IsAlgClosed K] in
/-- Completion preserves every original modular principal-part class. -/
theorem coeff_completion_principalParts_bijective
    (v : Place K (modularFunctionFieldCoeff N K)) :
    Function.Bijective v.completionPrincipalPartsMap := v.completionPrincipalPartsMap_bijective

/-- The actual completed integral space has a retraction extending the original projection. -/
theorem coeff_completion_integral_retraction
    (v : Place K (modularFunctionFieldCoeff N K)) :
    ∃ r : v.adicCompletion →ₗ[K] v.completionPlace.integralFunctions,
      (∀ a : v.completionPlace.integralFunctions, r a = a) ∧
      (∀ x : modularFunctionFieldCoeff N K,
        (r (algebraMap (modularFunctionFieldCoeff N K) v.adicCompletion x) : v.adicCompletion) =
          algebraMap (modularFunctionFieldCoeff N K) v.adicCompletion (v.tateProj x)) := by
  let hres := (coeff_place_residue_algebraMap_bijective N K v).surjective
  refine ⟨v.completionOriginalRetraction hres, v.completionOriginalRetraction_apply hres, ?_⟩
  exact v.completionOriginalProjection_algebraMap

end Dubon2026.SourceFunctionField

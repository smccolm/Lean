import Dubon2026.SourceCurveCompletionPrincipalParts

/-! An actual retraction of the completed field onto its integral ring,
using original principal parts. It extends the original integral
projection and makes the local finite-rank trace comparison explicit.
This serves residue/trace compatibility in the DUB-17/18 reverse-genus chain. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Extract the original finite principal part of a completed element. -/
def completionOriginalPrincipalPart : v.adicCompletion →ₗ[K] F :=
  v.principalPartLift ∘ₗ v.completionPrincipalPartsEquiv.symm.toLinearMap ∘ₗ
    v.completionPlace.integralFunctions.mkQ

/-- Original elements retain their original finite principal part. -/
theorem completionOriginalPrincipalPart_algebraMap (x : F) :
    v.completionOriginalPrincipalPart (algebraMap F v.adicCompletion x) =
      v.principalPart x := by
  change v.principalPartLift
    (v.completionPrincipalPartsEquiv.symm
      (v.completionPrincipalPartsEquiv (v.integralFunctions.mkQ x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Completed integral elements have zero original principal part. -/
theorem completionOriginalPrincipalPart_of_mem {x : v.adicCompletion}
    (hx : x ∈ v.adicCompletionIntegers) : v.completionOriginalPrincipalPart x = 0 := by
  have hq : v.completionPlace.integralFunctions.mkQ x = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  simp only [completionOriginalPrincipalPart, LinearMap.comp_apply, hq, map_zero]

/-- Removing the extracted original principal part leaves a completed integral element. -/
theorem completion_sub_principalPart_mem
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (x : v.adicCompletion) :
    x - algebraMap F v.adicCompletion (v.completionOriginalPrincipalPart x) ∈
      v.adicCompletionIntegers := by
  apply (Submodule.Quotient.mk_eq_zero v.completionPlace.integralFunctions).mp
  change v.completionPlace.integralFunctions.mkQ
    (x - algebraMap F v.adicCompletion (v.completionOriginalPrincipalPart x)) = 0
  rw [map_sub, sub_eq_zero]
  change v.completionPlace.integralFunctions.mkQ x =
    v.completionPrincipalPartsEquiv
      (v.integralFunctions.mkQ
        (v.principalPartLift
          (v.completionPrincipalPartsEquiv.symm (v.completionPlace.integralFunctions.mkQ x))))
  rw [v.mkQ_principalPartLift hres, LinearEquiv.apply_symm_apply]

/-- The completed integral projection obtained from original finite principal parts. -/
def completionOriginalProjection : v.adicCompletion →ₗ[K] v.adicCompletion :=
  LinearMap.id - v.completionLinearMap ∘ₗ v.completionOriginalPrincipalPart

/-- The completed projection extends the literal original projection. -/
theorem completionOriginalProjection_algebraMap (x : F) :
    v.completionOriginalProjection (algebraMap F v.adicCompletion x) =
      algebraMap F v.adicCompletion (v.tateProj x) := by
  change algebraMap F v.adicCompletion x -
    algebraMap F v.adicCompletion (v.completionOriginalPrincipalPart
      (algebraMap F v.adicCompletion x)) = _
  rw [v.completionOriginalPrincipalPart_algebraMap, ← map_sub]
  rfl

/-- The completed projection fixes every completed integral element. -/
theorem completionOriginalProjection_of_mem {x : v.adicCompletion}
    (hx : x ∈ v.adicCompletionIntegers) : v.completionOriginalProjection x = x := by
  change x - algebraMap F v.adicCompletion (v.completionOriginalPrincipalPart x) = x
  rw [v.completionOriginalPrincipalPart_of_mem hx, map_zero, sub_zero]

/-- The original-principal-part projection takes values in the actual completed integral space. -/
def completionOriginalRetraction
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    v.adicCompletion →ₗ[K] v.completionPlace.integralFunctions :=
  v.completionOriginalProjection.codRestrict _ (v.completion_sub_principalPart_mem hres)

/-- The constructed completed integral retraction is a left inverse of the inclusion. -/
theorem completionOriginalRetraction_apply
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (a : v.completionPlace.integralFunctions) : v.completionOriginalRetraction hres a = a :=
  Subtype.ext (v.completionOriginalProjection_of_mem a.2)

end Dubon2026.SourceCurve.Place

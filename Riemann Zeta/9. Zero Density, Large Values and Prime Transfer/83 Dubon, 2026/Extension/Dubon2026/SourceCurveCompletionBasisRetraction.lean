import Dubon2026.SourceCurveCompletionIntegralCoordinates
import Dubon2026.SourceCurveLocalMatrixTrace

/-! The constructed integral basis transfers the actual base integral
retraction to the extension. Its multiplication operators become the
literal multiplication matrices on integral coordinates. This is the
local field-trace reduction required by DUB-17/18 global residues. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- Apply the actual base integral retraction in each coordinate of the integral basis. -/
def completionBasisRetraction (D : w.CompletionIntegralBasis (F := F))
    (hres : Function.Surjective (algebraMap K (w.restrict F).completionPlace.ResidueField)) :
    w.adicCompletion →ₗ[K] w.completionPlace.integralFunctions :=
  (w.completionIntegralCoordinates D).symm.toLinearMap ∘ₗ
    LinearMap.pi (fun i => (w.restrict F).completionPlace.integralRetraction hres ∘ₗ
      LinearMap.proj i ∘ₗ (w.completionBasisCoordinates D).toLinearMap)

/-- The constructed retraction has exactly the coordinatewise base projection. -/
theorem completionBasisRetraction_coordinates (D : w.CompletionIntegralBasis (F := F))
    (hres : Function.Surjective (algebraMap K (w.restrict F).completionPlace.ResidueField))
    (x : w.adicCompletion)
    (i : Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion)) :
    w.completionIntegralCoordinates D (w.completionBasisRetraction D hres x) i =
      (w.restrict F).completionPlace.integralRetraction hres (D.basis.equivFun x i) := by
  change (w.completionIntegralCoordinates D)
    ((w.completionIntegralCoordinates D).symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The basis retraction fixes the actual completed integral space. -/
theorem completionBasisRetraction_apply (D : w.CompletionIntegralBasis (F := F))
    (hres : Function.Surjective (algebraMap K (w.restrict F).completionPlace.ResidueField))
    (a : w.completionPlace.integralFunctions) : w.completionBasisRetraction D hres a = a := by
  apply (w.completionIntegralCoordinates D).injective
  funext i
  rw [w.completionBasisRetraction_coordinates]
  exact (w.restrict F).completionPlace.integralRetraction_apply hres
    (w.completionIntegralCoordinates D a i)

/-- The multiplication matrix of an actual completed extension element in the integral basis. -/
def completionMultiplicationMatrix (D : w.CompletionIntegralBasis (F := F))
    (f : w.adicCompletion) :
    Matrix (Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion))
      (Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion))
        (w.restrict F).adicCompletion :=
  LinearMap.toMatrix D.basis D.basis
    (Algebra.lmul (w.restrict F).adicCompletion w.adicCompletion f)

/-- The actual multiplication matrix computes every field coordinate. -/
theorem completionMultiplicationMatrix_apply (D : w.CompletionIntegralBasis (F := F))
    (f x : w.adicCompletion)
    (i : Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion)) :
    D.basis.equivFun (f * x) i =
      ∑ j, w.completionMultiplicationMatrix D f i j * D.basis.equivFun x j := by
  change D.basis.repr
    (Algebra.lmul (w.restrict F).adicCompletion w.adicCompletion f x) i = _
  rw [← LinearMap.toMatrix_mulVec_repr D.basis D.basis]
  rfl

end Dubon2026.SourceCurve.Place

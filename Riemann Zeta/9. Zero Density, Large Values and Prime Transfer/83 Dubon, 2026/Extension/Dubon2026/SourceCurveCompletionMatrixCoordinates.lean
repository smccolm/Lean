import Dubon2026.SourceCurveCompletionBasisRetraction

/-! Integral coordinates identify actual multiplication in the completed
extension with its multiplication matrix, and base-field multiplication
with a diagonal operator. This supplies the exact operators needed by the
proved matrix commutator trace in DUB-17/18 residue compatibility. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The inverse integral-coordinate map has exactly the prescribed field coordinates. -/
theorem completionIntegralCoordinates_symm (D : w.CompletionIntegralBasis (F := F))
    (y : Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion) →
      (w.restrict F).completionPlace.integralFunctions)
    (i : Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion)) :
    D.basis.equivFun ((w.completionIntegralCoordinates D).symm y : w.adicCompletion) i =
      (y i : (w.restrict F).adicCompletion) :=
  congrArg Subtype.val (congrFun ((w.completionIntegralCoordinates D).apply_symm_apply y) i)

/-- Integral-coordinate conjugation gives the literal multiplication matrix operator. -/
theorem completionIntegralCoordinates_conj_lmul (D : w.CompletionIntegralBasis (F := F))
    (hres : Function.Surjective (algebraMap K (w.restrict F).completionPlace.ResidueField))
    (f : w.adicCompletion) :
    (w.completionIntegralCoordinates D).conj
      (projectedEnd w.completionPlace.integralFunctions (w.completionBasisRetraction D hres)
        (Algebra.lmul K w.adicCompletion f)) =
      (w.restrict F).completionPlace.integralMatrixEnd
        ((w.restrict F).completionPlace.integralRetraction hres)
          (w.completionMultiplicationMatrix D f) := by
  apply LinearMap.ext
  intro y
  funext i
  change w.completionIntegralCoordinates D
    (w.completionBasisRetraction D hres
      (f * ((w.completionIntegralCoordinates D).symm y : w.adicCompletion))) i = _
  rw [w.completionBasisRetraction_coordinates, w.completionMultiplicationMatrix_apply]
  simp only [w.completionIntegralCoordinates_symm, map_sum]
  change _ = blockEnd _ y i
  rw [blockEnd_apply]
  rfl

/-- Base-field multiplication becomes the literal common diagonal operator. -/
theorem completionIntegralCoordinates_conj_scalar (D : w.CompletionIntegralBasis (F := F))
    (hres : Function.Surjective (algebraMap K (w.restrict F).completionPlace.ResidueField))
    (g : (w.restrict F).adicCompletion) :
    (w.completionIntegralCoordinates D).conj
      (projectedEnd w.completionPlace.integralFunctions (w.completionBasisRetraction D hres)
        (Algebra.lmul K w.adicCompletion
          (algebraMap (w.restrict F).adicCompletion w.adicCompletion g))) =
      diagonalEnd (projectedEnd (w.restrict F).completionPlace.integralFunctions
        ((w.restrict F).completionPlace.integralRetraction hres)
          (Algebra.lmul K (w.restrict F).adicCompletion g)) := by
  apply LinearMap.ext
  intro y
  funext i
  change w.completionIntegralCoordinates D
    (w.completionBasisRetraction D hres
      (algebraMap (w.restrict F).adicCompletion w.adicCompletion g *
        ((w.completionIntegralCoordinates D).symm y : w.adicCompletion))) i = _
  rw [w.completionBasisRetraction_coordinates, ← Algebra.smul_def, map_smul,
    Pi.smul_apply, smul_eq_mul, w.completionIntegralCoordinates_symm]
  rfl

end Dubon2026.SourceCurve.Place

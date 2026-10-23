import Dubon2026.SourceCurveCompletionMatrixCoordinates
import Dubon2026.SourceCurveCompletionResidueField
import Dubon2026.SourceCurveConjugateCommutator

/-! The actual completed extension satisfies the local residue/field-trace
identity. Integral basis coordinates reduce the commutator to the proved
matrix calculation. This is the local extension input to the trace sum
over places and hence DUB-17/18 global residue vanishing. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The literal multiplication matrix has the actual field trace. -/
theorem completionMultiplicationMatrix_trace (D : w.CompletionIntegralBasis (F := F))
    (f : w.adicCompletion) :
    Matrix.trace (w.completionMultiplicationMatrix D f) =
      Algebra.trace (w.restrict F).adicCompletion w.adicCompletion f := by
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace _ D.basis]
  rfl

/-- Integral basis coordinates prove the actual completed local field-trace identity. -/
theorem completion_tateResidue_fieldTrace (D : w.CompletionIntegralBasis (F := F))
    (hresW : Function.Surjective (algebraMap K w.completionPlace.ResidueField))
    (hresV : Function.Surjective (algebraMap K (w.restrict F).completionPlace.ResidueField))
    (f : w.adicCompletion) (g : (w.restrict F).adicCompletion)
    (hg : g ∈ (w.restrict F).adicCompletionIntegers) :
    w.completionPlace.tateResidue f
      (algebraMap (w.restrict F).adicCompletion w.adicCompletion g) =
        (w.restrict F).completionPlace.tateResidue
          (Algebra.trace (w.restrict F).adicCompletion w.adicCompletion f) g := by
  let e := w.completionIntegralCoordinates D
  let r := w.completionBasisRetraction D hresV
  let rv := (w.restrict F).completionPlace.integralRetraction hresV
  let A := projectedEnd w.completionPlace.integralFunctions r (Algebra.lmul K w.adicCompletion f)
  let B := projectedEnd w.completionPlace.integralFunctions r (Algebra.lmul K w.adicCompletion
    (algebraMap (w.restrict F).adicCompletion w.adicCompletion g))
  let M := (w.restrict F).completionPlace.integralMatrixEnd rv (w.completionMultiplicationMatrix D f)
  let G := diagonalEnd
    (ι := Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion))
    (projectedEnd (w.restrict F).completionPlace.integralFunctions rv
    (Algebra.lmul K (w.restrict F).adicCompletion g))
  have hga : algebraMap (w.restrict F).adicCompletion w.adicCompletion g ∈ w.adicCompletionIntegers :=
    w.adicCompletionComap_mem_integers hg
  obtain ⟨hfin, htrace⟩ := w.completionPlace.tateResidue_eq_retraction_trace hresW r
    (w.completionBasisRetraction_apply D hresV) f
    (algebraMap (w.restrict F).adicCompletion w.adicCompletion g) hga
  haveI : FiniteDimensional K (LinearMap.range (A ∘ₗ B - B ∘ₗ A)) := hfin
  have hA := w.completionIntegralCoordinates_conj_lmul (F := F) D hresV f
  have hB := w.completionIntegralCoordinates_conj_scalar (F := F) D hresV g
  change e.conj A = M at hA
  change e.conj B = G at hB
  have heq := conjugate_commutator_eq e A B M G hA hB
  obtain ⟨_, hm⟩ := (w.restrict F).completionPlace.integralMatrixEnd_trace hresV rv
    ((w.restrict F).completionPlace.integralRetraction_apply hresV)
    (w.completionMultiplicationMatrix D f) g hg
  calc
    _ = finrankTrace (A ∘ₗ B - B ∘ₗ A) := htrace
    _ = finrankTrace (e.conj (A ∘ₗ B - B ∘ₗ A)) := (finrankTrace_conj e _).symm
    _ = finrankTrace (M ∘ₗ G - G ∘ₗ M) := congrArg finrankTrace heq
    _ = (w.restrict F).completionPlace.tateResidue
        (Matrix.trace (w.completionMultiplicationMatrix D f)) g := hm
    _ = _ := by rw [w.completionMultiplicationMatrix_trace]

end Dubon2026.SourceCurve.Place

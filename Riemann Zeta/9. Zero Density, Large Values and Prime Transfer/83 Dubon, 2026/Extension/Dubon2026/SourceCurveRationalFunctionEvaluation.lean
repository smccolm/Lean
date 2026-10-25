import Dubon2026.SourceCurveRationalEvaluation

/-! DUB-17/18 -> Weil reciprocity and Hecke adjointness -> norm evaluation.
Extend actual rational residue evaluation to field elements using the same
zero-at-poles convention as the existing original modular-field evaluation. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Actual rational place evaluation, with value zero assigned at poles. -/
def rationalEval (v : Place K F)
    (hv : Function.Bijective (algebraMap K v.ResidueField)) (f : F) : K := by
  classical
  exact if hf : f ∈ v.toValuationSubring then v.rationalRegularEval hv ⟨f, hf⟩ else 0

theorem rationalEval_of_mem (v : Place K F)
    (hv : Function.Bijective (algebraMap K v.ResidueField)) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.rationalEval hv f = v.rationalRegularEval hv ⟨f, hf⟩ := by
  classical
  exact dif_pos hf

theorem rationalEval_algebraMap (v : Place K F)
    (hv : Function.Bijective (algebraMap K v.ResidueField)) (a : K) :
    v.rationalEval hv (algebraMap K F a) = a := by
  rw [rationalEval_of_mem v hv (v.algebraMap_mem' a)]
  exact rationalRegularEval_algebraMap v hv a

end
end Dubon2026.SourceCurve.Place

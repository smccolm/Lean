import Dubon2026.SourceCurveRationalFunctionEvaluation
import Dubon2026.SourceCurveResidueRestriction

/-! DUB-17/18 -> original Weil reciprocity and Hecke adjointness ->
evaluation on pushed-forward divisors. The already constructed local
inclusion and residue-field map prove evaluation compatibility directly.
No new valuation comparison or residue-map construction is required. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [Algebra.IsIntegral F E]

theorem rationalRegularEval_restrictInclusion (w : Place K E)
    (hv : Function.Bijective (algebraMap K (w.restrict F).ResidueField))
    (hw : Function.Bijective (algebraMap K w.ResidueField))
    (f : (w.restrict F).toValuationSubring) :
    w.rationalRegularEval hw (w.restrictInclusion F f) =
      (w.restrict F).rationalRegularEval hv f := by
  apply hw.injective
  rw [residue_rationalRegularEval, ← restrictResidueMap_residue,
    ← residue_rationalRegularEval (w.restrict F) hv f]
  exact (IsScalarTower.algebraMap_apply K (w.restrict F).ResidueField w.ResidueField _).symm

theorem rationalEval_algebraMap_restrict (w : Place K E)
    (hv : Function.Bijective (algebraMap K (w.restrict F).ResidueField))
    (hw : Function.Bijective (algebraMap K w.ResidueField)) (f : F) :
    w.rationalEval hw (algebraMap F E f) = (w.restrict F).rationalEval hv f := by
  classical
  by_cases hf : f ∈ (w.restrict F).toValuationSubring
  · rw [rationalEval_of_mem _ hw (w.mem_restrict_iff.mp hf), rationalEval_of_mem _ hv hf]
    exact rationalRegularEval_restrictInclusion w hv hw ⟨f, hf⟩
  · have hf' : algebraMap F E f ∉ w.toValuationSubring := fun h => hf (w.mem_restrict_iff.mpr h)
    simp only [rationalEval, dif_neg hf, dif_neg hf']

end
end Dubon2026.SourceCurve.Place

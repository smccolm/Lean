import Dubon2026.SourceCurveCompletionLocalFieldTrace
import Dubon2026.SourceCurveCompletionTateTrace
import Dubon2026.SourceCurveResidueRestrictionConstants

/-! Discharge the integral-basis and both completed residue-rationality
premises in the local field-trace identity. The original finite separable
extension supplies the basis; the upper residue field supplies the lower
one. The source uniformizer case feeds the sum over places for DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  (w : Place K E)

/-- The derived completed field trace computes original residues against integral base elements. -/
theorem tateResidue_completion_fieldTrace
    (hres : Function.Surjective (algebraMap K w.ResidueField)) (f : E) (g : F)
    (hg : g ∈ (w.restrict F).toValuationSubring) :
    w.tateResidue f (algebraMap F E g) =
      (w.restrict F).completionPlace.tateResidue
        (Algebra.trace (w.restrict F).adicCompletion w.adicCompletion
          (algebraMap E w.adicCompletion f))
        (algebraMap F (w.restrict F).adicCompletion g) := by
  obtain ⟨D⟩ := w.completionIntegralBasis_nonempty (F := F)
  have hresV := w.residue_algebraMap_surjective_restrict (F := F) hres
  rw [← w.completion_tateResidue hres]
  rw [← w.adicCompletionComap_algebraMap]
  exact w.completion_tateResidue_fieldTrace D
    (w.completionPlace_residue_algebraMap_surjective hres)
    ((w.restrict F).completionPlace_residue_algebraMap_surjective hresV) _ _
    (((w.restrict F).completion_integer_iff g).mpr hg)

/-- The source base-uniformizer case needs no integrality or basis input from the caller. -/
theorem tateResidue_completion_fieldTrace_uniformizer
    (hres : Function.Surjective (algebraMap K w.ResidueField)) (f : E) :
    w.tateResidue f (algebraMap F E (w.restrict F).uniformizer) =
      (w.restrict F).completionPlace.tateResidue
        (Algebra.trace (w.restrict F).adicCompletion w.adicCompletion
          (algebraMap E w.adicCompletion f))
        (algebraMap F (w.restrict F).adicCompletion (w.restrict F).uniformizer) :=
  w.tateResidue_completion_fieldTrace hres f _ (w.restrict F).uniformizerSubring.2

end Dubon2026.SourceCurve.Place

import Dubon2026.SourceCurveCompletionIntegralCoordinates
import Dubon2026.SourceCurveCompletionResidueField
import Dubon2026.SourceCurveResidueRestrictionConstants

/-! The completed integral extension is local and its actual residue-field
map commutes with the original constants. Rational upper residues force
the completed inertia degree to be one. This is the residue factor needed
in the dimension formula for the DUB-17/18 trace sum over places. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open IsDedekindDomain IsLocalRing

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The actual map between completed integral rings is local. -/
instance completionIntegralExtensionIsLocalHom :
    IsLocalHom (algebraMap (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers) where
  map_nonunit a ha := by
    apply (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (v := (w.restrict F).heightOneSpectrum) (K := F) (a := a)).mpr
    have h := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (v := w.heightOneSpectrum) (K := E)
      (a := algebraMap (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers a)).mp ha
    change Valued.v (w.adicCompletionComap (F := F) (a : (w.restrict F).adicCompletion)) = 1 at h
    rw [w.valued_adicCompletionComap] at h
    exact (pow_eq_one_iff_of_nonneg zero_le (w.ramificationIndex_pos (F := F)).ne').mp h

/-- Constants commute with the actual completed residue extension. -/
theorem completion_residue_extension_constants (c : K) :
    letI := w.completionIntegralExtensionIsLocalHom (F := F)
    letI : Algebra (w.restrict F).completionPlace.ResidueField w.completionPlace.ResidueField :=
      inferInstanceAs (Algebra (IsLocalRing.ResidueField (w.restrict F).adicCompletionIntegers)
        (IsLocalRing.ResidueField w.adicCompletionIntegers))
    algebraMap (w.restrict F).completionPlace.ResidueField w.completionPlace.ResidueField
      (algebraMap K (w.restrict F).completionPlace.ResidueField c) =
        algebraMap K w.completionPlace.ResidueField c := by
  letI := w.completionIntegralExtensionIsLocalHom (F := F)
  letI : Algebra (w.restrict F).completionPlace.ResidueField w.completionPlace.ResidueField :=
    inferInstanceAs (Algebra (IsLocalRing.ResidueField (w.restrict F).adicCompletionIntegers)
      (IsLocalRing.ResidueField w.adicCompletionIntegers))
  change residue w.adicCompletionIntegers
    (algebraMap (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers
      (algebraMap K (w.restrict F).completionPlace.toValuationSubring c)) =
    residue w.adicCompletionIntegers (algebraMap K w.completionPlace.toValuationSubring c)
  congr 1
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply K (w.restrict F).adicCompletion w.adicCompletion c).symm

/-- Rational original upper residues make the completed residue extension surjective. -/
theorem completion_residue_extension_surjective
    (hres : Function.Surjective (algebraMap K w.ResidueField)) :
    letI := w.completionIntegralExtensionIsLocalHom (F := F)
    letI : Algebra (w.restrict F).completionPlace.ResidueField w.completionPlace.ResidueField :=
      inferInstanceAs (Algebra (IsLocalRing.ResidueField (w.restrict F).adicCompletionIntegers)
        (IsLocalRing.ResidueField w.adicCompletionIntegers))
    Function.Surjective (algebraMap (w.restrict F).completionPlace.ResidueField
      w.completionPlace.ResidueField) := by
  letI := w.completionIntegralExtensionIsLocalHom (F := F)
  letI : Algebra (w.restrict F).completionPlace.ResidueField w.completionPlace.ResidueField :=
    inferInstanceAs (Algebra (IsLocalRing.ResidueField (w.restrict F).adicCompletionIntegers)
      (IsLocalRing.ResidueField w.adicCompletionIntegers))
  refine fun z => ?_
  obtain ⟨c, rfl⟩ := w.completionPlace_residue_algebraMap_surjective hres z
  exact ⟨algebraMap K (w.restrict F).completionPlace.ResidueField c,
    w.completion_residue_extension_constants c⟩

end Dubon2026.SourceCurve.Place

import Dubon2026.SourceCurveCompletionResidueApproximation

/-! Completion preserves the literal residue field. This discharges the
rational-residue premise for the completed Tate trace used in the original
modular curve's residue/field-trace comparison, hence global residues and
the reverse genus inequality in the DUB-17/18 good-reduction chain. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open IsDedekindDomain

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The original integral ring embeds locally in its actual completion. -/
instance completionIntegersIsLocalHom :
    IsLocalHom (algebraMap v.toValuationSubring v.adicCompletionIntegers) where
  map_nonunit a ha := by
    apply (v.adicValuation_coe_eq_one_iff a).mp
    rw [← v.valued_completion_algebraMap]
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (v := v.heightOneSpectrum) (K := F)
      (a := algebraMap v.toValuationSubring v.adicCompletionIntegers a)).mp ha

/-- The actual map of residue fields induced by completing the local ring. -/
def completionResidueMap : v.ResidueField →+* v.completionPlace.ResidueField :=
  @IsLocalRing.ResidueField.map v.toValuationSubring v.adicCompletionIntegers _ _ _ _
    (algebraMap v.toValuationSubring v.adicCompletionIntegers) v.completionIntegersIsLocalHom

/-- The completion residue map is induced by the literal map of integral elements. -/
theorem completionResidueMap_residue (a : v.toValuationSubring) :
    v.completionResidueMap (IsLocalRing.residue v.toValuationSubring a) =
      IsLocalRing.residue v.adicCompletionIntegers
        (algebraMap v.toValuationSubring v.adicCompletionIntegers a) := rfl

/-- Completion induces a bijection of the original residue field with the completed one. -/
theorem completionResidueMap_bijective : Function.Bijective v.completionResidueMap := by
  refine ⟨v.completionResidueMap.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := v.completion_integral_residue_surjective z
  exact ⟨IsLocalRing.residue v.toValuationSubring a, ha⟩

/-- The completion residue map fixes the original constant field. -/
theorem completionResidueMap_algebraMap (c : K) :
    v.completionResidueMap (algebraMap K v.ResidueField c) =
      algebraMap K v.completionPlace.ResidueField c := by
  change IsLocalRing.residue v.adicCompletionIntegers
    (algebraMap v.toValuationSubring v.adicCompletionIntegers
      (algebraMap K v.toValuationSubring c)) =
    IsLocalRing.residue v.adicCompletionIntegers
      (algebraMap K v.completionPlace.toValuationSubring c)
  congr 1

/-- Rational residues remain rational after completion, with no new residue-field premise. -/
theorem completionPlace_residue_algebraMap_surjective
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    Function.Surjective (algebraMap K v.completionPlace.ResidueField) := by
  intro z
  obtain ⟨a, rfl⟩ := v.completionResidueMap_bijective.surjective z
  obtain ⟨c, rfl⟩ := hres a
  exact ⟨c, (v.completionResidueMap_algebraMap c).symm⟩

end Dubon2026.SourceCurve.Place

import Dubon2026.SourceCurveResidueRestriction

/-! DUB-17/18 -> global residue identity -> finite-extension residue comparison.
If the upper actual place has rational residue field, then its restriction
does too: the induced field map is injective and commutes with constants.
This removes the lower residue-surjectivity input in the original extension.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [Algebra.IsIntegral F E] (w : Place K E)

theorem residue_algebraMap_surjective_restrict
    (hres : Function.Surjective (algebraMap K w.ResidueField)) :
    Function.Surjective (algebraMap K (w.restrict F).ResidueField) := by
  intro a
  obtain ⟨c, hc⟩ := hres (w.restrictResidueMap F a)
  refine ⟨c, (w.restrictResidueMap F).injective ?_⟩
  change algebraMap (w.restrict F).ResidueField w.ResidueField
    (algebraMap K (w.restrict F).ResidueField c) = w.restrictResidueMap F a
  rw [← IsScalarTower.algebraMap_apply]
  exact hc

end
end Dubon2026.SourceCurve.Place

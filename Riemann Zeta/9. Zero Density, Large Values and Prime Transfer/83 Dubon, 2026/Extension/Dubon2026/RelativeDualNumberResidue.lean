import Dubon2026.DualNumberOriginalResidue

/-! # True dual-number residues over the original local coefficient ring -/

namespace Dubon2026

noncomputable section

/-- The original residue map of a field is an equivalence of algebras over any given coefficient ring. -/
def fieldOriginalResidueAlgEquiv (O K : Type*) [CommRing O] [Field K] [Algebra O K] :
    K ≃ₐ[O] IsLocalRing.ResidueField K :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom O K (IsLocalRing.ResidueField K))
    ⟨(IsLocalRing.residue K).injective, IsLocalRing.residue_surjective⟩

/-- The actual dual numbers over the residue field have that same true residue field as an algebra over the original local ring. -/
def relativeDualNumberResidueEquiv (O : Type*) [CommRing O] [IsLocalRing O] :
    IsLocalRing.ResidueField (DualNumber (IsLocalRing.ResidueField O)) ≃ₐ[O]
      IsLocalRing.ResidueField O := by
  let K := IsLocalRing.ResidueField O
  let f := TrivSqZeroExt.fstHom O K K
  have hf : Function.Surjective f := fun k => ⟨TrivSqZeroExt.inl k, rfl⟩
  letI : IsLocalHom f.toRingHom := IsLocalHom.of_surjective f.toRingHom hf
  exact (surjectiveLocalResidueAlgEquiv f hf).trans (fieldOriginalResidueAlgEquiv O K).symm

/-- Reduction through the true original relative dual-number residue equivalence is exactly the first coordinate. -/
theorem relativeDualNumberResidueEquiv_reduction (O : Type*) [CommRing O] [IsLocalRing O]
    (z : DualNumber (IsLocalRing.ResidueField O)) :
    localCoefficientReduction (relativeDualNumberResidueEquiv O) z = z.fst := by
  change (fieldOriginalResidueAlgEquiv O (IsLocalRing.ResidueField O)).symm
    ((fieldOriginalResidueAlgEquiv O (IsLocalRing.ResidueField O)) z.fst) = z.fst
  exact (fieldOriginalResidueAlgEquiv O (IsLocalRing.ResidueField O)).symm_apply_apply z.fst

/-- The original coefficient ring acts on its residual dual numbers by its own residue map followed by the constant inclusion. -/
theorem relativeDualNumber_algebraMap (O : Type*) [CommRing O] [IsLocalRing O] (o : O) :
    algebraMap O (DualNumber (IsLocalRing.ResidueField O)) o =
      TrivSqZeroExt.inl (IsLocalRing.residue O o) := rfl

end
end Dubon2026

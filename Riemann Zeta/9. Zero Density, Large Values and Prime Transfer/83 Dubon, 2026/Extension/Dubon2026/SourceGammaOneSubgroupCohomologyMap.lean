import Dubon2026.SourceGammaOneTransferCosetFormula

/-! DUB-17/18 -> original all-weight adic association -> actual Gamma1
surjective-transfer Hecke compatibility -> identify the existing subgroup
H1 isomorphism with its literal native pullback, without changing transfer. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup
open scoped Classical

private theorem coefficientIso_reindex_hom
    {R G H : Type} [CommRing R] [Group G] [Group H]
    {A B : Rep.{0} R H} (e : A ≅ B) (φ : G ≃* H) :
    ((groupCohomology.functor R H 1).mapIso e ≪≫
      originalCohomologyReindex B φ 1).hom =
      groupCohomology.map φ.toMonoidHom ((Rep.resFunctor φ.toMonoidHom).map e.hom) 1 := by
  change (groupCohomology.map (MonoidHom.id H) e.hom 1 ≫
    groupCohomology.map φ.toMonoidHom (𝟙 (Rep.res φ.toMonoidHom B)) 1) =
    groupCohomology.map φ.toMonoidHom ((Rep.resFunctor φ.toMonoidHom).map e.hom) 1
  rw [← groupCohomology.map_comp]
  rfl

/-- The existing subgroup H1 isomorphism is exactly native pullback along
the actual range isomorphism with the existing restricted coefficient trivialization. -/
theorem sourceGammaOneSubgroupH1Iso_hom_eq_map (Q N w : ℕ) [NeZero N] :
    (sourceGammaOneSubgroupH1Iso Q N w).hom =
      groupCohomology.map
        (A := Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
          (sourceBinaryCoefficientRep (ZMod N) Q w))
        (sourceGammaOneRangeEquiv Q N).toMonoidHom
        ((Rep.resFunctor (sourceGammaOneRangeEquiv Q N).toMonoidHom).map
          (sourceGammaOneCoefficientTrivialIso Q N w).hom) 1 := by
  exact coefficientIso_reindex_hom (sourceGammaOneCoefficientTrivialIso Q N w)
    (sourceGammaOneRangeEquiv Q N)

/-- The already proved surjective transfer applied to the existing
subgroup H1 identification is the original literal H1 trace, pointwise. -/
theorem sourceGammaOneConstantH1Transfer_subgroupIso
    (Q N w : ℕ) [NeZero Q] [NeZero N] :
    let H := (sourceGammaOneDiagonalHom Q N).range
    letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
    letI : Fintype (Gamma0 Q ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
    ∀ x : groupCohomology.H1 (Rep.res H.subtype (sourceBinaryCoefficientRep (ZMod N) Q w)),
      sourceGammaOneConstantH1Transfer Q N w ((sourceGammaOneSubgroupH1Iso Q N w).hom x) =
        sourceHeckeH1Trace (sourceBinaryCoefficientRep (ZMod N) Q w) H x := by
  let H := (sourceGammaOneDiagonalHom Q N).range
  letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
  letI : Fintype (Gamma0 Q ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  dsimp only
  intro x
  rw [sourceGammaOneConstantH1Transfer_eq_trace]
  change sourceHeckeH1Trace (sourceBinaryCoefficientRep (ZMod N) Q w) H
    ((sourceGammaOneSubgroupH1Iso Q N w).toLinearEquiv.symm
      ((sourceGammaOneSubgroupH1Iso Q N w).toLinearEquiv x)) = _
  rw [LinearEquiv.symm_apply_apply]

end
end Dubon2026

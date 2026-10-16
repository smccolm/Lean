import Dubon2026.OriginalFullIdeleCompletionH2

/-! # Literal cocycles for original full-idele completion localization

Identify the existing inverse-isomorphism localization with the direct
map using the actual completion restriction and actual idele coordinate.
This permits the local base-change computation required for the auxiliary
class restriction in DUB-17, without assuming a compatibility formula.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
attribute [-instance] UniformSpace.Completion.instSMul
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The actual idele coordinate intertwines the original completion Galois action. -/
def originalFullIdeleCompletionRepHom :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    Rep.res (originalCompletionGaloisRestriction K L v w) (originalFullIdeleRep K L) ⟶
      Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  refine Rep.ofHom ⟨(numberFieldIdeleFiniteComponent L w).toAdditive.toIntLinearMap, ?_⟩
  intro σ
  apply LinearMap.ext
  intro x
  obtain ⟨τ, rfl⟩ := (originalAdicDecompositionGaloisEquiv K L v w).surjective σ
  have h := Rep.hom_comm_apply (originalFullIdeleAdicRepHom K L w) τ x
  simpa only [originalCompletionGaloisRestriction, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using h

/-- The original completion localization is exactly the map on literal full-idele cocycles. -/
theorem originalFullIdeleCompletionH2_eq_map
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    originalFullIdeleCompletionH2 K L v w x =
      groupCohomology.map (originalCompletionGaloisRestriction K L v w)
        (originalFullIdeleCompletionRepHom K L v w) 2 x := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  apply (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.injective
  change (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv
      ((originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.symm
        (originalFullIdeleAdicH2 K L w x)) = _
  rw [LinearEquiv.apply_symm_apply]
  change originalFullIdeleAdicH2 K L w x =
    (originalAdicUnitCohomologyIso K L v w 2).hom
      (groupCohomology.map (originalCompletionGaloisRestriction K L v w)
        (originalFullIdeleCompletionRepHom K L v w) 2 x)
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [originalAdicUnitCohomologyIso, originalCohomologyReindex,
      Iso.trans_hom, Functor.mapIso_hom, asIso_hom, ModuleCat.comp_apply,
      groupCohomology.functor_map, originalFullIdeleAdicH2,
      groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    change Additive.ofMul (numberFieldIdeleFiniteComponent L w
      (c (g.1.val, g.2.val)).toMul) =
      Additive.ofMul (numberFieldIdeleFiniteComponent L w
        (c (((originalAdicDecompositionGaloisEquiv K L v w).symm
          (originalAdicDecompositionGaloisEquiv K L v w g.1)).val,
          ((originalAdicDecompositionGaloisEquiv K L v w).symm
            (originalAdicDecompositionGaloisEquiv K L v w g.2)).val)).toMul)
    simp only [MulEquiv.symm_apply_apply]

end
end Dubon2026

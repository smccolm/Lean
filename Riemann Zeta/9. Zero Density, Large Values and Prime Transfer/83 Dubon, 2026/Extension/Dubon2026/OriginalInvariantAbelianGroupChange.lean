import Dubon2026.OriginalFundamentalNormGroupChange
import Dubon2026.OriginalInvariantAbelianTrace

/-! # The actual invariant norm map under compatible group change

The proved fundamental diagram and evaluation at one give the literal
abelianization-inclusion square. This is the local/global map comparison
needed to send local inertia into the global outside-unit image in
DUB-17's prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable {G : Type} [Group G] [Fintype G]
  (S : Subgroup G) [S.Normal] [Fintype S] [Fintype (G ⧸ S)]
  (C : Rep.{0} ℤ S) (D : Rep.{0} ℤ G) (ℓ : C ⟶ Rep.res S.subtype D)
  (φ : groupCohomology.cocycles₂ C) (ψ : groupCohomology.cocycles₂ D)
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
  (hC : ∀ T : Subgroup S,
    Limits.IsZero (groupCohomology (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 2))
  (hD : ∀ T : Subgroup G,
    Limits.IsZero (groupCohomology (Rep.res T.subtype (originalFundamentalSplittingModule D ψ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res T.subtype (originalFundamentalSplittingModule D ψ)) 2))

/-- Compatibility of the actual H2 classes gives the literal
invariant-norm-map square with relative trace and abelianization inclusion. -/
theorem originalInvariantAbelianMap_groupChange
    (hclass : groupCohomology.map (MonoidHom.id S) ℓ 2 (groupCohomology.H2π C φ) =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype D)) 2 (groupCohomology.H2π D ψ))
    (x : C.ρ.invariants) :
    originalInvariantAbelianMap D ψ p hG hD
      (originalInvariantRelativeTrace D S ((Rep.invariantsFunctor ℤ S).map ℓ x)) =
      (Abelianization.map S.subtype).toAdditive
        (originalInvariantAbelianMap C φ p (hG.to_subgroup S) hC x) := by
  let MS := Rep.trivial ℤ S ℤ
  let MG := Rep.trivial ℤ G ℤ
  let χ := (originalTrivialSourceInvariantEquiv C).symm x
  let xI : ((Rep.ihom MG).obj D).quotientToInvariants S :=
    ⟨(χ ≫ ℓ).hom.toLinearMap, originalMorphism_internalHom_invariant MS (Rep.res S.subtype D) (χ ≫ ℓ)⟩
  let χD := originalFundamentalSubgroupTraceMorphism MG D S xI
  let FD := originalFundamentalHomologyLinear MG D ψ p hG hD
  let FC := originalFundamentalHomologyLinear MS C φ p (hG.to_subgroup S) hC
  have heval : originalSubgroupTrivialSourceInvariantEquiv D S xI =
      (Rep.invariantsFunctor ℤ S).map ℓ x := by
    apply Subtype.ext
    change ℓ.hom (χ.hom 1) = ℓ.hom x.val
    exact congrArg ℓ.hom (congrArg Subtype.val
      ((originalTrivialSourceInvariantEquiv C).apply_symm_apply x))
  have hχD : (originalTrivialSourceInvariantEquiv D).symm
      (originalInvariantRelativeTrace D S ((Rep.invariantsFunctor ℤ S).map ℓ x)) = χD := by
    apply (originalTrivialSourceInvariantEquiv D).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    have he := originalSubgroupTraceMorphism_eval D S xI
    rw [heval] at he
    exact he.symm
  have hh := originalFundamentalHomology_groupChange S C D ℓ φ ψ p hG hC hD hclass χ
  calc
    _ = originalTrivialDualHomologyEquiv G (FD χD) :=
      congrArg (fun v => originalTrivialDualHomologyEquiv G (FD v)) hχD
    _ = originalTrivialDualHomologyEquiv G (groupHomology.map S.subtype (𝟙 _) 1 (FC χ)) :=
      congrArg (originalTrivialDualHomologyEquiv G) hh
    _ = _ := originalTrivialDualHomologyEquiv_map S.subtype (FC χ)

end
end Dubon2026

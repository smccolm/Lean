import Dubon2026.LocalFieldSurjectiveBaseInvariant
import Dubon2026.GaloisUnitBaseChangeComposition

/-! # Normalized invariant scaling for the actual finite base field

Identify the given local field with its image in the same closure and use
the existing finite-intermediate-field scaling and surjective-base
transport theorems. This is required for the actual completion fields in
DUB-17's auxiliary-class restriction; those fields are not subtypes of
the chosen closure.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- Genuine finite base change multiplies the normalized local invariant by the actual base-field degree. -/
theorem localFieldContinuousInvariant_actual_finite_restriction
    (K E Ω : Type) [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
    [FiniteDimensional K E] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω x := by
  letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  let φ := IsScalarTower.toAlgHom K E Ω
  let F : IntermediateField K Ω := φ.fieldRange
  let e : E ≃ₐ[K] F := AlgEquiv.ofInjective φ φ.injective
  letI : FiniteDimensional K F := Module.Finite.equiv e.toLinearEquiv
  letI : Algebra F E := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq' (by
    ext y
    exact (e.symm.commutes y).symm)
  letI : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq' (by
    ext y
    change y.val = (e (e.symm y)).val
    rw [e.apply_symm_apply])
  letI : IsGalois F Ω := IsGalois.tower_top_of_isGalois K F Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F Ω) := ⟨rfl⟩
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  obtain ⟨hval, htop⟩ := localField_local_structures_eq_spectral K E
  cases hval
  cases htop
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : NormedAlgebra F E := spectralNorm.normedAlgebra' K F E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  haveI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation E) :=
    normedFieldValuation_hasExtension F E
  have hs : Function.Surjective (algebraMap F E) := e.symm.surjective
  have hF := localFieldContinuousH2InvariantEquiv_finite_restriction K Ω F x
  have hE := localFieldContinuousInvariant_surjective_baseChange F E Ω hs
    (continuousGaloisUnitBaseChangeH2 K F Ω Ω x)
  rw [continuousGaloisUnitBaseChangeH2_comp K F E Ω Ω Ω] at hE
  exact hE.trans (hF.trans (congrArg
    (fun n : ℕ => n • localFieldContinuousH2InvariantEquiv K Ω x)
      e.toLinearEquiv.finrank_eq.symm))

end
end Dubon2026

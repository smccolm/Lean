import Dubon2026.LocalFieldFiniteTrivialCocycles
import Dubon2026.ContinuousCocycleRestrictionFiniteness
import Dubon2026.ContinuousFiniteCoefficientSplitting
import Dubon2026.FiniteCoefficientFixingCocycles
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.SpectralFiniteExtensionLocalField

/-! # Finiteness of actual local H1 for finite prime-field coefficient modules

The original action is allowed to be nontrivial. Its actual finite splitting
field, constant cocycle finiteness and finite coset determination prove the
finiteness input required for the trace-zero local duality route in DUB-17.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] continuousTrivialCoordinateSMul

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (A : Rep (ZMod q) Gal(Ω/K))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

include hA in
/-- All actual continuous cocycles in the original finite prime-field module
form a finite set. No trivial-action, splitting-field or H1 finiteness premise
is assumed; the original local field supplies each required finite input. -/
theorem localField_finiteCoefficientCocycles (hq : (q : K) ≠ 0) :
    Finite (continuousRepresentationCocyclesOne A) := by
  obtain ⟨F, hF⟩ := continuousFiniteCoefficient_exists_splittingField A hA
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  haveI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : IsGalois F Ω := IsGalois.tower_top_of_isGalois K F Ω
  have hqF : (q : F) ≠ 0 := by
    intro hz
    apply hq
    apply (algebraMap K F).injective
    simpa only [map_natCast, map_zero] using hz
  haveI : Finite (continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation (ZMod q) Gal(Ω/F) A))) :=
    localField_finiteTrivialCocycles F Ω A q hqF
  haveI : Finite (continuousRepresentationCocyclesOne
      (restrictedCoefficientRep A F.toIntermediateField.fixingSubgroup.subtype)) :=
    Finite.of_equiv _ (finiteCoefficientFixingCocycleEquiv K Ω q A F.toIntermediateField
      (fun g a => hF g g.property a)).symm.toEquiv
  exact continuousCocyclesOne_finite_of_restriction A F.toIntermediateField.fixingSubgroup

/-- The full original continuous H1 of a finite prime-field module is finite,
as the genuine quotient of the proved finite original cocycle space. -/
theorem localField_finiteCoefficientH1 (hq : (q : K) ≠ 0) :
    Finite (ContinuousRepresentationH1 A hA) := by
  haveI := localField_finiteCoefficientCocycles K Ω q A hA hq
  exact Finite.of_surjective (continuousRepresentationCoboundariesOne A hA).mkQ
    (Submodule.mkQ_surjective _)

end
end Dubon2026

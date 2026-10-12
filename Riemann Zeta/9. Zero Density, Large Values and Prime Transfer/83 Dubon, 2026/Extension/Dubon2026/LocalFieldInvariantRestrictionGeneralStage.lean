import Dubon2026.ContinuousGaloisRestrictionGeneralStage
import Dubon2026.LocalFieldContinuousInvariantNormalization
import Dubon2026.LocalFieldInvariantBaseChange

/-! # The original local invariant on unramified representatives over arbitrary bases -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- If an original unramified finite representative is embedded in
a genuine unramified stage over the new base, restriction multiplies its
full original invariant by the degree of that base. Normality of E/K is
not assumed. The finite and infinite maps act on the actual cocycles. -/
theorem localFieldContinuousInvariant_restriction_general_stage
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω)
    (G : FiniteGaloisIntermediateField E Ω)
    [Algebra F G] [IsScalarTower K F G] [IsScalarTower F G Ω]
    [ValuativeRel E] [ValuativeRel F] [ValuativeRel G]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField F]
    [IsNonarchimedeanLocalField G]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation G)]
    [(ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation G)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]]
    [Algebra.FormallyUnramified 𝒪[E] 𝒪[G]]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (y : GaloisUnitH2FiniteStage K Ω F) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω
        (continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F y)) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω
        (galoisUnitH2FiniteStageMap K Ω F y) := by
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E G) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E G) := ⟨rfl⟩
  have hres := continuousGaloisUnitRestriction_general_stage E F G y
  have hE := localFieldContinuousH2InvariantEquiv_stage E Ω G (finiteGaloisUnitBaseChangeH2 K E F G y)
  have hF := localFieldContinuousH2InvariantEquiv_stage K Ω F y
  have hbase := localFieldPeriodRationalInvariant_baseChange K E F G y
  exact (congrArg (localFieldContinuousH2InvariantEquiv E Ω) hres).trans
    (hE.trans (hbase.trans (congrArg (fun q : AddCircle (1 : ℚ) => Module.finrank K E • q) hF.symm)))

end
end Dubon2026

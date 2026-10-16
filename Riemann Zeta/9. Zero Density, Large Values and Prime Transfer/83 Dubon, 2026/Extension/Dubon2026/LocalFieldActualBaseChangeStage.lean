import Dubon2026.ContinuousGaloisBaseChangeFiniteStage
import Dubon2026.LocalFieldContinuousInvariantNormalization
import Dubon2026.LocalFieldInvariantBaseChange

/-! # Actual local base change on original unramified finite stages

The original completion and its orbit field are distinct field types.
This applies the existing finite invariant formula to their literal maps,
using the already proved composition and finite-stage inflation identities.
It is the finite-stage step of DUB-17's normalized completion comparison.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K E Ω : Type) [Field K] [Field E] [Field Ω]
  [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
  [IsGalois K Ω] [IsGalois E Ω] [IsSepClosed Ω]
  [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
  (F : FiniteGaloisIntermediateField K Ω) (G : FiniteGaloisIntermediateField E Ω)
  [Algebra K G] [Algebra F G] [IsScalarTower K E G] [IsScalarTower K F G] [IsScalarTower F G Ω]
  [ValuativeRel F] [ValuativeRel G] [TopologicalSpace F] [TopologicalSpace G]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField G]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation G)]
  [(ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation G)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]] [Algebra.FormallyUnramified 𝒪[E] 𝒪[G]]

include G in
/-- Literal base change of an original finite-stage class has the existing normalized degree formula. -/
theorem localFieldContinuousInvariant_actual_baseChange_stage
    (y : GaloisUnitH2FiniteStage K Ω F) :
    localFieldContinuousH2InvariantEquiv E Ω
      (continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F y)) =
        Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω
          (galoisUnitH2FiniteStageMap K Ω F y) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E G) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E G) := ⟨rfl⟩
  have hleft : continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F y) =
      continuousGaloisUnitBaseChangeH2 K E F Ω y :=
    (congrArg (continuousGaloisUnitBaseChangeH2 K E Ω Ω)
      (continuousGaloisUnitBaseChangeH2_eq_finiteStage K Ω F y).symm).trans
        (continuousGaloisUnitBaseChangeH2_comp K K E F Ω Ω y)
  have hright : continuousGaloisUnitBaseChangeH2 E E G Ω
      (finiteGaloisUnitBaseChangeH2 K E F G y) = continuousGaloisUnitBaseChangeH2 K E F Ω y :=
    continuousGaloisUnitBaseChangeH2_comp K E E F G Ω y
  have hstage := continuousGaloisUnitBaseChangeH2_eq_finiteStage E Ω G
    (finiteGaloisUnitBaseChangeH2 K E F G y)
  have hres := hleft.trans (hright.symm.trans hstage)
  have hE := localFieldContinuousH2InvariantEquiv_stage E Ω G (finiteGaloisUnitBaseChangeH2 K E F G y)
  have hF := localFieldContinuousH2InvariantEquiv_stage K Ω F y
  have hbase := localFieldPeriodRationalInvariant_baseChange K E F G y
  exact (congrArg (localFieldContinuousH2InvariantEquiv E Ω) hres).trans
    (hE.trans (hbase.trans (congrArg (fun q : AddCircle (1 : ℚ) => Module.finrank K E • q) hF.symm)))

end
end Dubon2026

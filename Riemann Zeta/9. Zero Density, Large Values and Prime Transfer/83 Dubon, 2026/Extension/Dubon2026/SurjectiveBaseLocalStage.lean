import Dubon2026.SurjectiveBaseGaloisStage
import Dubon2026.LocalFieldValuativeExtensionUniqueness

/-! # Retain the original local structures on an identical rebased stage

The normalized completion comparison for DUB-17 uses the existing
unramified finite stage with exactly its original valuation and topology.
These named transports keep that identity explicit through Lean's
dependent field structures; they do not choose new local data.
-/
namespace Dubon2026
noncomputable section

variable (K E Ω : Type) [Field K] [Field E] [Field Ω]
  [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
  (h : Function.Surjective (algebraMap K E)) (F : FiniteGaloisIntermediateField K Ω)

/-- The unchanged stage retains its literal original valuation relation. -/
abbrev surjectiveBaseLocalStageValuation (v : ValuativeRel F) :
    ValuativeRel (surjectiveBaseGaloisStage K E Ω h F) := v

/-- The unchanged stage retains its literal original topology. -/
abbrev surjectiveBaseLocalStageTopology (t : TopologicalSpace F) :
    TopologicalSpace (surjectiveBaseGaloisStage K E Ω h F) := t

/-- The retained original local structures still satisfy the local-field property. -/
theorem surjectiveBaseLocalStage_isLocal
    [v : ValuativeRel F] [t : TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    letI := surjectiveBaseLocalStageValuation K E Ω h F v
    letI := surjectiveBaseLocalStageTopology K E Ω h F t
    IsNonarchimedeanLocalField (surjectiveBaseGaloisStage K E Ω h F) :=
  inferInstanceAs (IsNonarchimedeanLocalField F)

end
end Dubon2026

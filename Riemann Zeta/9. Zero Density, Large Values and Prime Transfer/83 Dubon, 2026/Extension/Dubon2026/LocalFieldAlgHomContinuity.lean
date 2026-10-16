import Dubon2026.LocalFieldAlgHomValuationComparison
import Dubon2026.OriginalLocalScalarContinuity

/-! # Continuity of the actual local embeddings used in completion towers

The proved valuation comparison supplies the native extension instance.
Reuse the existing original-scalar continuity theorem. This is needed to
identify the completed orbit-field inclusions with the original completed
global field map in DUB-17's finite-global localization comparison.
-/
namespace Dubon2026
noncomputable section

variable (K E M : Type) [Field K] [Field E] [Field M]
  [Algebra K E] [Algebra K M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- The literal common-base local-field embedding is continuous for the original topologies. -/
theorem localFieldAlgHom_continuous (f : E →ₐ[K] M) : Continuous f := by
  letI : Algebra E M := f.toAlgebra
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M) :=
    ⟨localFieldAlgHom_valuation_isEquiv K E M f⟩
  exact originalLocalScalar_continuous E M

end
end Dubon2026

import Dubon2026.OriginalGlobalCompletionH2FiniteSupport
import Dubon2026.OriginalCompletionCarryInvariant

/-! # Original local vanishing kills the normalized completion invariant

Reuse the original decomposition/completion comparison and the existing
normalized invariant. Together with proved finite support this removes
the corresponding local-invariant support premise in DUB-17's sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

/-- Vanishing of the original finite-prime localization forces its existing normalized completion invariant to vanish. -/
theorem originalGlobalCompletionInvariant_eq_zero_of_adic
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : originalGlobalAdicH2 K L w x = 0) :
    originalGlobalCompletionInvariant K L v w Ω x = 0 := by
  have hz := originalGlobalCompletionH2_eq_zero_of_adic K L v w x hx
  unfold originalGlobalCompletionInvariant
  rw [hz]
  simp only [map_zero]

end
end Dubon2026

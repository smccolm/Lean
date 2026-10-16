import Dubon2026.OriginalCompletionCarryInvariant

/-! # The literal finite-global cocycle at its original completion

The existing algebraic localization cocycle is continuous on the actual
finite completion Galois group. Naming it retains the same original
values and lets the finite-global comparison reuse its checked interface
without expanding the completion construction inside each H2 argument.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The literal finite completion unit coefficients have their discrete topology. -/
local instance originalCompletionCoefficientTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
/-- The specified finite completion coefficient topology is discrete. -/
local instance originalCompletionCoefficientDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩

/-- The original finite global cocycle localized at the actual completed fields, with its derived continuity. -/
def originalGlobalCompletionContinuousCocycle
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    continuousRepresentationCocyclesTwo
      (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) :=
  ⟨groupCohomology.mapCocycles₂ (originalCompletionGaloisRestriction K L v w)
    (originalGlobalCompletionUnitRepHom K L v w) c, continuous_of_discreteTopology⟩

/-- The continuous finite completion cocycle has exactly the original localized algebraic H2 class. -/
theorem originalGlobalCompletionH2_continuousCocycle
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    originalGlobalCompletionH2 K L v w (groupCohomology.H2π _ c) =
      continuousDiscreteH2Equiv
        (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
        (discreteGaloisUnitAction_continuous (K := v.adicCompletion K)
          (Ω := w.adicCompletion L))
        (Submodule.Quotient.mk (originalGlobalCompletionContinuousCocycle K L v w c)) :=
  groupCohomology.H2π_comp_map_apply _ _ c

end
end Dubon2026

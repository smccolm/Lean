import Dubon2026.OriginalCompletionGaloisAmbientComparison
import Dubon2026.OriginalGlobalCompletionCocycle

/-! # Equality of the original localized and direct ambient cocycles

The actual completion restriction comparison and scalar tower identify
both maps on every original two-cocycle value. This discharges the
cochain obligation in DUB-17's finite-global invariant comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryGalois
  originalCompletionCarryFinite originalCompletionCoefficientTopology originalCompletionCoefficientDiscrete

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower K L Ω] [IsScalarTower K (v.adicCompletion K) Ω]
  [IsScalarTower L (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

/-- Inflating the original finite completion cocycle gives exactly the direct ambient localization cocycle. -/
theorem originalGlobalCompletionContinuousCocycle_ambient
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    continuousGaloisUnitBaseChangeCocycle (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L) Ω (originalGlobalCompletionContinuousCocycle K L v w c.val) =
      continuousGaloisUnitBaseChangeCocycle K (v.adicCompletion K) L Ω c := by
  apply Subtype.ext
  apply groupCohomology.cocycles₂_ext
  intro g h
  change Additive.ofMul (Units.map (algebraMap (w.adicCompletion L) Ω).toMonoidHom
    (Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom
      (c.val (originalCompletionGaloisRestriction K L v w
        (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
          (w.adicCompletion L) Ω g),
        originalCompletionGaloisRestriction K L v w
          (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
            (w.adicCompletion L) Ω h))).toMul)) = _
  rw [originalCompletionGaloisRestriction_ambient K L v w Ω,
    originalCompletionGaloisRestriction_ambient K L v w Ω]
  apply congrArg Additive.ofMul
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply L (w.adicCompletion L) Ω _).symm

end
end Dubon2026

import Dubon2026.OriginalSPlaceLocalRelationInvariant
import Dubon2026.OriginalAdicLocalUnitRelationCup

/-! Name the actual finite-local cup invariant with its original completion
coefficient types. This keeps the arithmetic total consumer's type inference
local to that completion; it adds no comparison or mathematical hypothesis. -/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois
  originalAdicLocalRelationCupFinite originalCompletionCarryValuation originalCompletionCarryLocalField
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul finiteLocalRelationCoefficientTopology
  finiteLocalRelationCoefficientDiscrete finiteLocalRelationCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω] [Algebra (v.adicCompletion K) Ω]
  [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- The normalized invariant of the original local Hom cup evaluated at
the inflation of its actual finite completion H1 input. -/
def originalAdicFiniteLocalCupInvariant
    (c : continuousRepresentationCocyclesOne (originalAdicLocalCoefficientUnitHom K L v w Ω B))
    (x : galoisTowerFiniteLocalCoefficientH1 (v.adicCompletion K) (w.adicCompletion L)
      Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w) B) : AddCircle (1 : ℚ) :=
  localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
    (galoisTowerLocalUnitCup (v.adicCompletion K) (w.adicCompletion L) Ω
      Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w) B c
      (galoisTowerFiniteLocalH1Inflation (v.adicCompletion K) (w.adicCompletion L) Ω
        Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w) B x))

end
end Dubon2026

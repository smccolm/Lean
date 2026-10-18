import Dubon2026.OriginalAdicLocalUnitRelationCup

/-! An explicit statement of the original local relation/cup conclusion.
This predicate is not a proof or an additional assumption. It keeps the
actual Cartier specialization readable without repeatedly elaborating its
full arithmetic cohomology carrier in DUB-17's local construction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV2
attribute [local instance] originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois
  originalAdicLocalRelationCupFinite originalAdicRelationCupHomTopology
  originalAdicRelationCupHomDiscrete originalAdicRelationCupHomContinuousSMul

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω] [Algebra (v.adicCompletion K) Ω]
  [Algebra (w.adicCompletion L) Ω] [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- One original relation morphism represents every actual continuous
unit cup with the specified local cocycle. This is only the conclusion's statement. -/
def OriginalAdicLocalUnitCupRealization
    (c : continuousRepresentationCocyclesOne (originalAdicLocalCoefficientUnitHom K L v w Ω B)) : Prop :=
  let j := originalAdicCompletionGaloisInclusion K L v w
  ∃ ψ : Rep.res j (originalRelationModule B) ⟶
    Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L),
    ∀ x : galoisTowerLocalCoefficientH1 (v.adicCompletion K) (w.adicCompletion L) Ω Gal(L/K) j B,
      galoisTowerLocalUnitCup (v.adicCompletion K) (w.adicCompletion L) Ω Gal(L/K) j B c x =
        galoisTowerLocalUnitRelationConnecting (v.adicCompletion K) (w.adicCompletion L) Ω
          Gal(L/K) j B ψ x

end
end Dubon2026

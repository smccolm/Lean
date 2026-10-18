import Dubon2026.OriginalAdicLocalUnitRelationCup
import Dubon2026.GaloisTowerLocalRelationFiniteComparison

/-! The constructed actual completion-unit relation represents the local
cup on every original finite-stage H1 input, through genuine continuous
base change of the same finite connecting obstruction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois
  originalAdicLocalRelationCupFinite originalAdicRelationCupHomTopology
  originalAdicRelationCupHomDiscrete originalAdicRelationCupHomContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω] [Algebra (v.adicCompletion K) Ω]
  [Algebra (w.adicCompletion L) Ω] [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- One constructed same-completion relation realizes every original finite-stage local cup. -/
theorem originalAdicLocalUnitCocycle_exists_finite_relation_cup
    (c : continuousRepresentationCocyclesOne (originalAdicLocalCoefficientUnitHom K L v w Ω B)) :
    let ι := originalAdicCompletionGaloisInclusion K L v w
    ∃ ψ : Rep.res ι (originalRelationModule B) ⟶
      Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L),
      ∀ x : galoisTowerFiniteLocalCoefficientH1 (v.adicCompletion K) (w.adicCompletion L) Gal(L/K) ι B,
        galoisTowerLocalUnitCup (v.adicCompletion K) (w.adicCompletion L) Ω Gal(L/K) ι B c
          (galoisTowerFiniteLocalH1Inflation (v.adicCompletion K) (w.adicCompletion L) Ω Gal(L/K) ι B x) =
        continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
          (w.adicCompletion L) Ω
          (galoisTowerFiniteLocalRelationConnecting (v.adicCompletion K) (w.adicCompletion L)
            Gal(L/K) ι B ψ x) := by
  obtain ⟨ψ, hψ⟩ := originalAdicLocalUnitCocycle_exists_relation_cup K L v w Ω B c
  refine ⟨ψ, fun x => ?_⟩
  exact (hψ (galoisTowerFiniteLocalH1Inflation (v.adicCompletion K) (w.adicCompletion L) Ω
    Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w) B x)).trans
    (galoisTowerLocalRelationConnecting_eq_finite_baseChange (v.adicCompletion K)
      (w.adicCompletion L) Ω Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w) B ψ x)

end
end Dubon2026

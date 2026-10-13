import Dubon2026.SpectralUnramifiedPrimeExtension

/-! # Constructed unramified enlargement kills original finite-coefficient H2

This discharges the tower-existence hypothesis in the finite-stage vanishing
needed for unramified local support, global reciprocity and DUB-17 Selmer duality.
It does not assert the still-unproved global reciprocity or global exactness.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
  (q : ℕ) [Fact q.Prime] (A : Rep (ZMod q) Gal(F/K)) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(F/K) × A => A.ρ z.1 z.2))

include hF

/-- Every original finite-coefficient H2 class over an actual unramified stage
vanishes in a constructed larger unramified stage. Neither the larger field,
its containment, its degree, cyclicity nor H2 vanishing is an input. -/
theorem spectralUnramifiedH2_exists_zero_inflation :
    ∃ E : FiniteGaloisIntermediateField K Ω, ∃ hFE : F ≤ E,
      SpectralStageUnramified K Ω E ∧
        letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
        letI : IsScalarTower K F E := IsScalarTower.of_algHom (IntermediateField.inclusion hFE)
        ∀ x : ContinuousRepresentationH2 A hA,
          continuousRepresentationH2Restriction A hA
            (AlgEquiv.restrictNormalHom F : Gal(E/K) →* Gal(F/K))
            continuous_of_discreteTopology x = 0 := by
  obtain ⟨E, hFE, hE, hdegree⟩ := spectralUnramifiedStage_exists_prime_extension F hF q
  refine ⟨E, hFE, hE, ?_⟩
  letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
  haveI : IsScalarTower K F E := IsScalarTower.of_algHom (IntermediateField.inclusion hFE)
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  haveI : IsNonarchimedeanLocalField E := spectralFiniteExtension_isNonarchimedeanLocalField K E
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension K E
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[E] := hE
  intro x
  exact unramifiedCharacteristicH2Inflation_eq_zero K F E q A hA hdegree x

end
end Dubon2026

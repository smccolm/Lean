import Dubon2026.ArithmeticCyclotomicReciprocityAwayConductor

/-! # Local cyclicity away from a cyclotomic conductor

Unramifiedness makes the actual local Galois group cyclic even when the
global cyclotomic Galois group is not cyclic. The existing spectral-norm
construction and unramified reciprocity theorem supply the original local
character without a global cyclicity assumption. DUB-17 needs this for the
away-prime factors of the two-power containing field's principal product.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)
  (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)

include hpn

/-- Away from the conductor, the actual local-stage Galois group is cyclic;
no cyclicity of the global containing field is required. -/
theorem arithmeticCyclotomicFiniteLocalStage_isCyclic_away :
    IsCyclic Gal(rationalArithmeticFiniteLocalStage a F p hp /
      rationalPrimeLocalField p hp) := by
  let K := rationalPrimeLocalField p hp
  let M := rationalArithmeticFiniteLocalStage a F p hp
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  let normK := localFieldOriginalNorm K
  letI : NontriviallyNormedField K := normK
  letI : NormedField K := normK.toNormedField
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField M := spectralNorm.nontriviallyNormedField K M
  letI : NormedAlgebra K M := spectralNorm.normedAlgebra K M
  haveI : IsUltrametricDist M := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : IsNonarchimedeanLocalField M := spectralFiniteExtension_isNonarchimedeanLocalField K M
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M) :=
    spectralValuation_hasExtension K M
  letI := arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
  exact (unramifiedLocalFieldResidueGaloisEquiv K M).isCyclic.mpr inferInstance

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The original reciprocity character away from the conductor, with local
cyclicity and local-field structures derived and no global cyclicity premise. -/
theorem arithmeticCyclotomicContainingField_reciprocity_away
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (u : (rationalPrimeLocalField p hp)ˣ) :
    letI := arithmeticCyclotomicFiniteLocalStage_isCyclic_away a F p hp n hpn
    hζ.autToPow ℚ (rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp) (rationalArithmeticFiniteLocalStage a F p hp)
        (Additive.ofMul u)).toMul) =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) ^
        localFieldUnitOrder (rationalPrimeLocalField p hp) (Additive.ofMul u) := by
  let K := rationalPrimeLocalField p hp
  let M := rationalArithmeticFiniteLocalStage a F p hp
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  let normK := localFieldOriginalNorm K
  letI : NontriviallyNormedField K := normK
  letI : NormedField K := normK.toNormedField
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField M := spectralNorm.nontriviallyNormedField K M
  letI : NormedAlgebra K M := spectralNorm.normedAlgebra K M
  haveI : IsUltrametricDist M := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : IsNonarchimedeanLocalField M := spectralFiniteExtension_isNonarchimedeanLocalField K M
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M) :=
    spectralValuation_hasExtension K M
  exact arithmeticCyclotomicFiniteLocal_reciprocity_character a F p hp n hpn hζ u

end
end Dubon2026

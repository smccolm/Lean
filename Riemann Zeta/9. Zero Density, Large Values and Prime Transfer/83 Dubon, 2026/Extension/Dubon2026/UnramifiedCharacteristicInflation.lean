import Dubon2026.CyclicGaloisCharacteristicInflation
import Dubon2026.UnramifiedLocalFieldResidueGalois
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Actual unramified local towers kill finite-coefficient H2

The genuine field-to-residue equivalence supplies cyclicity, and local-field
theory supplies finiteness. This removes the independent cyclicity input
from the finite-stage vanishing needed for unramified support in DUB-17's
global reciprocity and Selmer sequence.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K F E : Type) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
  [IsGalois K F] [IsGalois K E]
  [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[E]]
  (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) Gal(F/K)) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(F/K) × A => A.ρ z.1 z.2))

/-- In the actual unramified local Galois tower, characteristic-degree
enlargement kills every original finite-coefficient H2 class. The needed
finite cyclic structure is proved from the original local and residue fields. -/
theorem unramifiedCharacteristicH2Inflation_eq_zero
    (hdegree : Module.finrank F E = q) (x : ContinuousRepresentationH2 A hA) :
    letI : FiniteDimensional K E := localField_field_module_finite
    continuousRepresentationH2Restriction A hA
      (AlgEquiv.restrictNormalHom F : Gal(E/K) →* Gal(F/K))
      continuous_of_discreteTopology x = 0 := by
  letI : FiniteDimensional K E := localField_field_module_finite
  haveI : IsCyclic Gal(E/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K E).isCyclic.mpr inferInstance
  exact cyclicGaloisCharacteristicH2Inflation_eq_zero K F E q A hA hdegree x

end
end Dubon2026

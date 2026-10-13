import Dubon2026.SpectralUnramifiedH2Effacement
import Dubon2026.ContinuousH2RestrictionComposition

/-! # Actual absolute inflation of an unramified finite-stage H2 class vanishes

The constructed unramified enlargement and original restriction composition
remove the finite-stage class on the actual absolute Galois group. To obtain
finite arithmetic support one must still prove that the original local classes
come from such unramified stages away from the exceptional primes.
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

/-- Original absolute inflation kills each original finite-coefficient H2
class from a genuine unramified stage. The proof uses a constructed field
enlargement and the actual Galois restriction maps, not an assumed vanishing. -/
theorem spectralUnramifiedH2_absolute_inflation_eq_zero
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K))
      (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) x = 0 := by
  obtain ⟨E, hFE, _hE, hzero⟩ := spectralUnramifiedH2_exists_zero_inflation F hF q A hA
  letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
  haveI : IsScalarTower K F E := IsScalarTower.of_algHom (IntermediateField.inclusion hFE)
  haveI : IsScalarTower F E Ω := .of_algebraMap_eq' rfl
  let j : Gal(E/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  let k : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hj : Continuous j := continuous_of_discreteTopology
  have hk : Continuous k := InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField
  let T (f : Gal(Ω/K) →* Gal(F/K)) : Prop :=
    ∀ hf : Continuous f, continuousRepresentationH2Restriction A hA f hf x = 0
  have hz : T (j.comp k) := by
    intro hf
    rw [continuousRepresentationH2Restriction_comp A hA j hj k hk x]
    rw [hzero x, map_zero]
  have heq : (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K)) = j.comp k :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp K F E Ω
  exact (Eq.mp (congrArg T heq.symm) hz)
    (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField)

end
end Dubon2026

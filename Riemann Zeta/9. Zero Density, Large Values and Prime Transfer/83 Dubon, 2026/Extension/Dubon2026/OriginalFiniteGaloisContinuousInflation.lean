import Dubon2026.ContinuousGaloisBaseChangeFiniteStage
import Dubon2026.ContinuousGaloisUnitFiniteStageInjection

/-! # Actual finite Galois fields inject into original continuous unit H2

The existing finite-intermediate-stage injection is applied to the image
of the actual original finite field. A genuine degree-one finite tower
and literal base-change composition retain the original coefficient and
maps. This lets DUB-17's local invariant killing theorem descend from a
common closure to the actual original finite completion extension.
-/
namespace Dubon2026
noncomputable section

private theorem actualSameBase_finiteInflation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousGaloisUnitBaseChangeH2 K K L M x = finiteGaloisUnitTowerH2Inflation K L M x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousGaloisUnitBaseChangeH2_mk, finiteGaloisUnitTowerH2Inflation_mk]
    congr 1

/-- Literal continuous unit H2 inflation from any original finite Galois field into the actual original Galois extension is injective. -/
theorem originalFiniteGalois_continuousH2Inflation_injective
    (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [FiniteDimensional K L] [IsGalois K L] [IsGalois K Ω]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] :
    Function.Injective (continuousGaloisUnitBaseChangeH2 K K L Ω) := by
  let φ := IsScalarTower.toAlgHom K L Ω
  let F₀ : IntermediateField K Ω := φ.fieldRange
  let e₀ : L ≃ₐ[K] F₀ := AlgEquiv.ofInjective φ φ.injective
  letI : FiniteDimensional K F₀ := Module.Finite.equiv e₀.toLinearEquiv
  letI : IsGalois K F₀ := IsGalois.of_algEquiv e₀
  let F : FiniteGaloisIntermediateField K Ω := ⟨F₀⟩
  let e : L ≃ₐ[K] F := e₀
  letI : Algebra L F := e.toRingHom.toAlgebra
  letI : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact congrArg (fun y : F => (y : Ω)) (e.commutes x).symm)
  letI : IsScalarTower L F Ω := IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  have hinj : Function.Injective (continuousGaloisUnitBaseChangeH2 K K F Ω) := by
    intro x y hxy
    apply galoisUnitFiniteStageH2Inflation_injective F
    change galoisUnitH2FiniteStageMap K Ω F x = galoisUnitH2FiniteStageMap K Ω F y
    rwa [← continuousGaloisUnitBaseChangeH2_eq_finiteStage,
      ← continuousGaloisUnitBaseChangeH2_eq_finiteStage]
  intro x y hxy
  apply finiteGaloisUnitTowerH2Inflation_injective K L F
  rw [← actualSameBase_finiteInflation, ← actualSameBase_finiteInflation]
  apply hinj
  rwa [continuousGaloisUnitBaseChangeH2_comp K K K L F Ω,
    continuousGaloisUnitBaseChangeH2_comp K K K L F Ω]

end
end Dubon2026

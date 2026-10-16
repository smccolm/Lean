import Dubon2026.ArithmeticOriginalPrimeFiniteSupport
import Dubon2026.ArithmeticOriginalPrimeInvariantSum
import Mathlib.Algebra.BigOperators.Finprod

/-! # Original finite-stage odd-primary number-field reciprocity

Inflation preserves the actual finite-stage cohomological annihilator.
The proved individual-prime support and exact prime-indexed Mackey sum
then give the genuine original-prime total, with no support or zero-sum
assumption. This discharges the odd-primary finite-stage reciprocity input
on DUB-17's full-order-class route; the full-order class remains separate.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitUpperGalois
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

omit [FiniteDimensional ℚ F] in
/-- The actual finite-stage H2 annihilator is preserved by its original continuous inflation. -/
theorem rationalArithmeticFiniteStageInflation_nsmul_eq_zero
    (n : ℕ) (y : rationalArithmeticFiniteStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
      letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
      letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      n • (Submodule.Quotient.mk z :
        GaloisUnitContinuousH2 (K := F) (Ω := H)) = 0) :
    n • (Submodule.Quotient.mk (rationalArithmeticFiniteStageInflation a F H hFH y) :
      GaloisUnitContinuousH2 (K := F) (Ω := rationalUnramifiedExtension a)) = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
  change n • (Submodule.Quotient.mk (continuousGaloisUnitBaseChangeCocycle F F H
    (rationalUnramifiedExtension a) z) : GaloisUnitContinuousH2 (K := F) (Ω := rationalUnramifiedExtension a)) = 0
  let j := continuousGaloisUnitBaseChangeH2 F F H (rationalUnramifiedExtension a)
  have hz : n • (Submodule.Quotient.mk z : GaloisUnitContinuousH2 (K := F) (Ω := H)) = 0 := hy
  have hj : n • j (Submodule.Quotient.mk z) = 0 :=
    (map_nsmul j n (Submodule.Quotient.mk z)).symm.trans
      ((congrArg j hz).trans (map_zero j))
  exact (congrArg (fun x : GaloisUnitContinuousH2 (K := F) (Ω := rationalUnramifiedExtension a) => n • x)
    (continuousGaloisUnitBaseChangeH2_mk F F H (rationalUnramifiedExtension a) z)).symm.trans hj

/-- Every actual odd-primary finite-stage class has finite original-prime support and zero total completion invariant. -/
theorem rationalArithmeticFiniteStage_invariants_exists_support_sum_zero
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : rationalArithmeticFiniteStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
      letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
      letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      q ^ (r + 1) • (Submodule.Quotient.mk z :
        GaloisUnitContinuousH2 (K := F) (Ω := H)) = 0) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)),
      (∀ w ∉ T, rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticFiniteStageInflation a F H hFH y) w = 0) ∧
      (∑ w ∈ T, rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticFiniteStageInflation a F H hFH y) w) = 0 := by
  letI : TopologicalSpace (rationalArithmeticUnitRepresentation a) := ⊥
  letI : DiscreteTopology (rationalArithmeticUnitRepresentation a) := ⟨rfl⟩
  obtain ⟨T, hT⟩ := rationalArithmeticOriginalPrimeInvariant_exists_support a F H hFH y
  exact ⟨T, hT, rationalArithmeticOriginalPrimeInvariant_sum_zero a F q r hq hq2 hqa
    (rationalArithmeticFiniteStageInflation a F H hFH y)
    (rationalArithmeticFiniteStageInflation_nsmul_eq_zero a F H hFH (q ^ (r + 1)) y hy) T hT⟩

/-- The genuine original-prime finsum of an actual odd-primary finite-stage class is zero, backed by its proved finite support. -/
theorem rationalArithmeticFiniteStage_invariants_finsum_zero
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : rationalArithmeticFiniteStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
      letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
      letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      q ^ (r + 1) • (Submodule.Quotient.mk z :
        GaloisUnitContinuousH2 (K := F) (Ω := H)) = 0) :
    (∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 F), rationalArithmeticOriginalPrimeInvariant a F
      (rationalArithmeticFiniteStageInflation a F H hFH y) w) = 0 := by
  obtain ⟨T, hT, hsum⟩ := rationalArithmeticFiniteStage_invariants_exists_support_sum_zero
    a F H hFH q r hq hq2 hqa y hy
  refine (finsum_eq_sum_of_support_subset _ ?_).trans hsum
  intro w hw
  by_contra h
  exact hw (hT w h)

end
end Dubon2026

import Dubon2026.ArithmeticRelativePrimePowerRealSum
import Dubon2026.ArithmeticRealCorestrictionInfiniteKernel
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant
import Dubon2026.ContinuousFiniteH2CardAnnihilation

/-! # The all-prime original principal kernel with zero infinite localization

The finite-stage degree supplies the exact annihilator; native inflation
preserves it and native original-prime localization supplies finite support.
The actual real corestriction vanishes by the proved original infinite
comparison. Thus the prime-power finite-plus-real sum kills the original
principal image, including the prime two. This is precisely the kernel
input for DUB-17's same-stage normalized full-order class construction.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

private theorem finiteDegree_annihilates_original_unit_class
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    (n : ℕ) (hn : Module.finrank K L = n)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) : n • x = 0 := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  have hz := continuousFiniteH2_card_nsmul_eq_zero (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x
  have he : Fintype.card Gal(L/K) = n :=
    Nat.card_eq_fintype_card.symm.trans ((IsGalois.card_aut_eq_finrank K L).trans hn)
  exact he ▸ hz

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

private theorem principal_cocycle_zero_of_infinite
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (y : rationalArithmeticRelativeStageCocycles a F H hFH)
    (hi : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      ∀ v : NumberField.InfinitePlace H,
        originalGlobalInfiniteH2 F H v (groupCohomology.H2π _ z.val) = 0) :
    rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH
      (rationalArithmeticRelativeStagePrincipalClass a F H hFH y) = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  letI : TopologicalSpace (rationalArithmeticUnitRepresentation a) := ⊥
  letI : DiscreteTopology (rationalArithmeticUnitRepresentation a) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ) := ⟨rfl⟩
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
  have hz := finiteDegree_annihilates_original_unit_class F H (q ^ (r + 1)) hdegree
    (Submodule.Quotient.mk z)
  have hs := rationalArithmeticRelativeStage_prime_power_finsum_add_real_zero a F H hFH q r hq hqa y hz
  have hr := rationalArithmeticRealCorestriction_eq_zero_of_infinite a F H hFH (hGal := hGal) y hi
  have hr0 : rationalArithmeticRelativeStageRealInvariant a F H hFH y = 0 :=
    (congrArg originalRealUnitH2Invariant hr).trans (map_zero originalRealUnitH2Invariant)
  rw [hr0, add_zero] at hs
  exact (finsum_congr (fun w =>
    rationalArithmeticRelativeStageIdelePrimeInvariant_principal a F H hFH y w)).trans hs

/-- For every prime dividing the ramification parameter, the actual
finite-stage principal image has zero finite total whenever its original
infinite localizations vanish; the degree derives the annihilator. -/
theorem rationalArithmeticRelativeStageIdeleTotalInvariant_principal_of_infinite
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∀ x : groupCohomology (Rep.ofAlgebraAutOnUnits F H) 2,
      (∀ v : NumberField.InfinitePlace H, originalGlobalInfiniteH2 F H v x = 0) →
      rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH
        ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H) x) = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : IsGalois F H := hGal
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  intro x
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    intro hi
    exact principal_cocycle_zero_of_infinite a F H hFH q r hq hqa hdegree
      (⟨c, continuous_of_discreteTopology⟩ : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H)) hi

end
end Dubon2026

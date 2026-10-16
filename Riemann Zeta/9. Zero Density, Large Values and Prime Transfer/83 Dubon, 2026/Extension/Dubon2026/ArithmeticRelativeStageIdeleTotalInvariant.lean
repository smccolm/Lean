import Dubon2026.ArithmeticRelativeStageIdelePrimeInvariant
import Dubon2026.ArithmeticRelativeStageReciprocity

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The sum of the actual normalized original-prime invariants is additive, using the proved finite support of every original full-idele class. -/
def rationalArithmeticRelativeStageIdeleTotalInvariant :
    rationalArithmeticRelativeStageIdeleH2 a F H hFH →+ AddCircle (1 : ℚ) where
  toFun x := ∑ᶠ w, rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w x
  map_zero' := finsum_eq_zero_of_forall_eq_zero (fun w => map_zero (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w))
  map_add' x y := (finsum_congr (fun w => map_add (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w) x y)).trans
    (finsum_add_distrib (rationalArithmeticRelativeStageIdelePrimeInvariant_hasFiniteSupport a F H hFH x)
      (rationalArithmeticRelativeStageIdelePrimeInvariant_hasFiniteSupport a F H hFH y))

/-- The total map is definitionally the sum of the same genuine original-prime coordinates. -/
theorem rationalArithmeticRelativeStageIdeleTotalInvariant_apply
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x =
      ∑ᶠ w, rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w x := rfl

/-- The original full-idele total vanishes on the actual principal image of every odd-primary finite-stage global class. -/
theorem rationalArithmeticRelativeStageIdeleTotalInvariant_principal
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : rationalArithmeticRelativeStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
      letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
      letI : IsGalois F H := hGal
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      q ^ (r + 1) • (Submodule.Quotient.mk z :
        GaloisUnitContinuousH2 (K := F) (Ω := H)) = 0) :
    rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH
      (rationalArithmeticRelativeStagePrincipalClass a F H hFH y) = 0 := by
  exact (finsum_congr (fun w => rationalArithmeticRelativeStageIdelePrimeInvariant_principal a F H hFH y w)).trans
    (rationalArithmeticRelativeStage_invariants_finsum_zero a F H hFH q r hq hq2 hqa y hy)

end
end Dubon2026

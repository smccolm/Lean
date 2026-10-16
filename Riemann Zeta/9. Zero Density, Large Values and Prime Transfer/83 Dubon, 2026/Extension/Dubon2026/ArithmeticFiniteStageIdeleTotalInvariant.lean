import Dubon2026.ArithmeticFiniteStageIdelePrimeInvariant
import Dubon2026.ArithmeticFiniteStageReciprocity

/-! # The actual finite-stage full-idele total and its principal kernel

Proved finite support makes the original-prime sum an additive map on
the genuine full-idele H2. Its value on the actual principal image is
zero by the proved odd-primary finite-stage reciprocity theorem. This
supplies DUB-17's principal-kernel input; descent through the original
class quotient and construction of a full-order class remain separate.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- The sum of the actual normalized original-prime invariants is additive, using the proved finite support of every original full-idele class. -/
def rationalArithmeticFiniteStageIdeleTotalInvariant :
    rationalArithmeticFiniteStageIdeleH2 a F H hFH →+ AddCircle (1 : ℚ) where
  toFun x := ∑ᶠ w, rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH w x
  map_zero' := finsum_eq_zero_of_forall_eq_zero (fun w => map_zero (rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH w))
  map_add' x y := (finsum_congr (fun w => map_add (rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH w) x y)).trans
    (finsum_add_distrib (rationalArithmeticFiniteStageIdelePrimeInvariant_hasFiniteSupport a F H hFH x)
      (rationalArithmeticFiniteStageIdelePrimeInvariant_hasFiniteSupport a F H hFH y))

/-- The total map is definitionally the sum of the same genuine original-prime coordinates. -/
theorem rationalArithmeticFiniteStageIdeleTotalInvariant_apply
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH) :
    rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x =
      ∑ᶠ w, rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH w x := rfl

/-- The original full-idele total vanishes on the actual principal image of every odd-primary finite-stage global class. -/
theorem rationalArithmeticFiniteStageIdeleTotalInvariant_principal
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
    rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH
      (rationalArithmeticFiniteStagePrincipalClass a F H hFH y) = 0 := by
  exact (finsum_congr (fun w => rationalArithmeticFiniteStageIdelePrimeInvariant_principal a F H hFH y w)).trans
    (rationalArithmeticFiniteStage_invariants_finsum_zero a F H hFH q r hq hq2 hqa y hy)

end
end Dubon2026

import Dubon2026.RationalTraceFiniteSUnitDualClass
import Dubon2026.RationalTraceFiniteTowerRepresentation

/-! Use the exact larger-field coefficient returned by the finite S-unit
correction in the original global trace-dual class construction. The native
finite tower action supplies the coefficient transport; none is assumed.
This is the actual finite-correction input for DUB-17 local recovery. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F N : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hFN : F.toIntermediateField ≤ N.toIntermediateField)
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The actual larger-stage S-unit relation gives an original global
trace-dual H1 class with its coefficient identification constructed. -/
def rationalTraceFiniteTowerSUnitDualClass :
    letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
    letI : Module F N := Algebra.toModule
    letI : SMul F N := Algebra.toSMul
    let τ : Gal(N/ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
    (originalRelationModule (Rep.res τ (rationalTraceOriginalFiniteRep a q σ F hker)) ⟶
      arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N) →
        RationalArithmeticTraceDualH1 a q hqa σ hσ := by
  letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
  letI : Module F N := Algebra.toModule
  letI : SMul F N := Algebra.toSMul
  letI : IsScalarTower ℚ F N := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
  let τ : Gal(N/ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  change (originalRelationModule (Rep.res τ (rationalTraceOriginalFiniteRep a q σ F hker)) ⟶
    arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N) →
      RationalArithmeticTraceDualH1 a q hqa σ hσ
  intro η
  let hkerN := finiteStageCoefficientKernel_mono
    (rationalArithmeticTraceZeroIntegerRep a q σ) F N hFN hker
  have hB := rationalTraceOriginalFinite_tower_representation a q σ F N hFN hker
  let ηN : originalRelationModule (rationalTraceOriginalFiniteRep a q σ N hkerN) ⟶
      arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N :=
    Eq.mpr (congrArg (fun V : Rep.{0} ℤ Gal(N/ℚ) =>
      originalRelationModule V ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N) hB) η
  exact rationalTraceFiniteSUnitDualClass a ha q σ N hkerN hσ hqa hn ηN

end
end Dubon2026

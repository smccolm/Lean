import Dubon2026.ArithmeticFiniteSUnitHomTowerH1
import Dubon2026.RationalTraceFiniteSUnitDualClass

/-! Construct the original global trace-dual H1 directly from the actual
finite correction in its returned restricted coefficient. The native
Galois-tower isomorphism identifies the unit-Hom classes; no equality
transport of the relation is needed. This retains the existential source
contract in DUB-17's reverse-localization proof. Prescribed restrictions
remain to be established by the actual local connecting comparisons. -/
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

attribute [local instance] rationalTraceFiniteDualClassAlgebraicClosure

/-- The returned finite correction directly constructs an original
global trace-dual class through the actual Galois-tower unit-Hom map. -/
def rationalTraceFiniteCorrectionDirectDualClass :
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
  let τ : Gal(N/ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  let BN := Rep.res τ B
  letI : Finite B := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  letI : Finite BN := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  have hB (b : BN) : q • b = 0 := by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  change (originalRelationModule BN ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N) →
    RationalArithmeticTraceDualH1 a q hqa σ hσ
  intro η
  let x : ArithmeticFiniteSUnitHomH1 a ha N BN :=
    arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa N BN hB η
  let y : RationalTraceFiniteSUnitHomH1 a ha q σ F hker :=
    arithmeticFiniteSUnitHomTowerH1Equiv a ha F N hFN B x
  exact rationalTraceFiniteSUnitHomH1Equiv a ha q σ F hker hσ hqa hn y

end
end Dubon2026

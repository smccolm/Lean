import Dubon2026.RationalTraceFiniteTowerAction
import Dubon2026.OriginalUnramifiedStageInUnion
import Dubon2026.ArithmeticOriginalRelationStagePlacement

/-! Identify the finite trace action at the original constructed ambient
stage with the action pulled back from its literal image in the union.
This discharges the coefficient comparison between DUB-17's zero Cartier
obstruction and the original relation-extension criterion. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois
  relationPlacementStageAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (P : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom P u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (N : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
  (i : P →ₐ[ℚ] N.val)
  (hi : ∀ x : P, (i x : AlgebraicClosure ℚ) = (x.val : AlgebraicClosure ℚ))

/-- The actual original-stage coefficient and the descended image
coefficient have the same action on every original trace-zero matrix. -/
theorem rationalTraceOriginalStageImage_action
    (g : Gal(N.val/ℚ)) (x : rationalArithmeticTraceZeroIntegerRep a q σ) :
    let M := originalUnramifiedStageInUnion a N
    let hPM := originalUnramifiedStageInUnion_contains_embedded a P N i hi
    let e := originalUnramifiedStageInUnionEquiv a N
    letI : Algebra M N.val := e.symm.toAlgHom.toAlgebra
    letI : Module M N.val := e.symm.toAlgHom.toAlgebra.toModule
    letI : SMul M N.val := e.symm.toAlgHom.toAlgebra.toSMul
    letI : IsScalarTower ℚ M N.val := IsScalarTower.of_algHom e.symm.toAlgHom
    (rationalTraceOriginalFiniteRep a q σ M
      (finiteStageCoefficientKernel_mono (rationalArithmeticTraceZeroIntegerRep a q σ)
        P M hPM hker)).ρ (AlgEquiv.restrictNormalHom M g) x =
      (arithmeticOriginalStageRestrictedCoefficient (AlgebraicClosure ℚ) a P N i
        (rationalTraceOriginalFiniteRep a q σ P hker)).ρ g x := by
  let M := originalUnramifiedStageInUnion a N
  let hPM := originalUnramifiedStageInUnion_contains_embedded a P N i hi
  let e := originalUnramifiedStageInUnionEquiv a N
  letI : Algebra M N.val := e.symm.toAlgHom.toAlgebra
  letI : Module M N.val := e.symm.toAlgHom.toAlgebra.toModule
  letI : SMul M N.val := e.symm.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ M N.val := IsScalarTower.of_algHom e.symm.toAlgHom
  letI : Algebra P M := (IntermediateField.inclusion hPM).toAlgebra
  letI : Module P M := Algebra.toModule
  letI : SMul P M := Algebra.toSMul
  letI : IsScalarTower ℚ P M := IsScalarTower.of_algHom (IntermediateField.inclusion hPM)
  letI : Algebra P N.val := i.toAlgebra
  letI : Module P N.val := i.toAlgebra.toModule
  letI : SMul P N.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ P N.val := IsScalarTower.of_algHom i
  letI : IsScalarTower P M N.val := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro z
    change i z = e.symm (IntermediateField.inclusion hPM z)
    apply e.injective
    rw [e.apply_symm_apply]
    exact DFunLike.congr_fun (originalUnramifiedStageInUnion_embedding_eq_inclusion a P N i hi) z)
  have h := finiteStageCoefficientRepresentation_restrict
    (rationalArithmeticTraceZeroIntegerRep a q σ) P M hPM hker
    (AlgEquiv.restrictNormalHom M g) x
  exact h.trans (congrArg (fun u => (rationalTraceOriginalFiniteRep a q σ P hker).ρ u x)
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply P M g).symm)

/-- The original-stage and image-stage coefficients are the same bundled
representation, so the original relation criterion can use the actual
descended trace coefficient without a supplied identification. -/
theorem rationalTraceOriginalStageImage_representation :
    let M := originalUnramifiedStageInUnion a N
    let hPM := originalUnramifiedStageInUnion_contains_embedded a P N i hi
    let e := originalUnramifiedStageInUnionEquiv a N
    letI : Algebra M N.val := e.symm.toAlgHom.toAlgebra
    letI : Module M N.val := e.symm.toAlgHom.toAlgebra.toModule
    letI : SMul M N.val := e.symm.toAlgHom.toAlgebra.toSMul
    letI : IsScalarTower ℚ M N.val := IsScalarTower.of_algHom e.symm.toAlgHom
    Rep.res (AlgEquiv.restrictNormalHom M : Gal(N.val/ℚ) →* Gal(M/ℚ))
      (rationalTraceOriginalFiniteRep a q σ M
        (finiteStageCoefficientKernel_mono (rationalArithmeticTraceZeroIntegerRep a q σ)
          P M hPM hker)) =
      arithmeticOriginalStageRestrictedCoefficient (AlgebraicClosure ℚ) a P N i
        (rationalTraceOriginalFiniteRep a q σ P hker) := by
  let M := originalUnramifiedStageInUnion a N
  let e := originalUnramifiedStageInUnionEquiv a N
  letI : Algebra M N.val := e.symm.toAlgHom.toAlgebra
  letI : Module M N.val := e.symm.toAlgHom.toAlgebra.toModule
  letI : SMul M N.val := e.symm.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ M N.val := IsScalarTower.of_algHom e.symm.toAlgHom
  apply congrArg (fun ρ : Representation ℤ Gal(N.val/ℚ)
    (rationalArithmeticTraceZeroIntegerRep a q σ) => Rep.of ρ)
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  exact rationalTraceOriginalStageImage_action a q σ P hker N i hi g x

end
end Dubon2026

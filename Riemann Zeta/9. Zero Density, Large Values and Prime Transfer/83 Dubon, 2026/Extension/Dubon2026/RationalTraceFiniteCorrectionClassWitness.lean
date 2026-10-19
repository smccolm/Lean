import Dubon2026.RationalTraceFiniteTowerSUnitDualClass
import Dubon2026.ArithmeticOriginalStageImageSUnitCorrection

/-! Retain the actual finite correction and the original global H1 class
it constructs in a single witness. This avoids discarding the finite
relation equation needed by DUB-17's local recovery argument. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois
  relationTransportUnionAlgebra relationTransportStageAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (N : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom (originalUnramifiedStageInUnion a N) u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The finite S-unit correction together with the exact original global
trace-dual class arising from that same correction. -/
abbrev RationalTraceOriginalImageGlobalClassWitness
    (ψ : originalRelationModule
      (rationalTraceOriginalFiniteRep a q σ (originalUnramifiedStageInUnion a N) hker) ⟶
        ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha (originalUnramifiedStageInUnion a N))
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ) : Prop :=
    let M := originalUnramifiedStageInUnion a N
    let B := rationalTraceOriginalFiniteRep a q σ M hker
    ∃ L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
      ∃ hML : M ≤ L,
        letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
        letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
        letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
        let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
        let ψL := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map ψ ≫
          arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML
        ∃ l : Rep.free ℤ Gal(L/ℚ) (Rep.res τ B) ⟶
          ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha L,
          ∃ η : originalRelationModule (Rep.res τ B) ⟶
            arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha L,
            (η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha L =
              ψL - originalRelationInclusion (Rep.res τ B) ≫ l) ∧
            rationalTraceFiniteTowerSUnitDualClass a ha q σ M L hML hker hσ hqa hn η = x

/-- Every actual finite correction supplies its original global H1
class while retaining the same relation equation and correction witness. -/
theorem rationalTraceFiniteCorrection_exists_global_class
    (ψ : originalRelationModule
      (rationalTraceOriginalFiniteRep a q σ (originalUnramifiedStageInUnion a N) hker) ⟶
        ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha (originalUnramifiedStageInUnion a N))
    (h : ArithmeticOriginalImageFiniteSUnitCorrectionResult (AlgebraicClosure ℚ) a ha N
      (rationalTraceOriginalFiniteRep a q σ (originalUnramifiedStageInUnion a N) hker) ψ) :
    ∃ x : RationalArithmeticTraceDualH1 a q hqa σ hσ,
      RationalTraceOriginalImageGlobalClassWitness a ha q σ N hker hσ hqa hn ψ x := by
  unfold ArithmeticOriginalImageFiniteSUnitCorrectionResult at h
  obtain ⟨L, hML, h⟩ := h
  let M := originalUnramifiedStageInUnion a N
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  obtain ⟨l, η, hη⟩ := h
  exact ⟨rationalTraceFiniteTowerSUnitDualClass a ha q σ M L hML hker hσ hqa hn η,
    L, hML, l, η, hη, rfl⟩

end
end Dubon2026

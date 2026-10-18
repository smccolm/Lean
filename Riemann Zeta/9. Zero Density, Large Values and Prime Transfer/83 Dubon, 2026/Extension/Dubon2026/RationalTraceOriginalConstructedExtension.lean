import Dubon2026.ArithmeticOriginalConstructedStageCriterion
import Dubon2026.RationalTraceOriginalStageImageAction
import Dubon2026.OriginalStageImageRelationObstruction

/-! Choose the actual original extension field and consume a zero class
obstruction on its literal image with the same descended trace coefficient.
This is the extension step between DUB-17's Cartier total calculation and
recovery of the prescribed local H1 classes. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois
  relationPlacementStageAlgebra

local instance rationalTraceConstructedExtensionAlgebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have h := AlgebraicClosure.instIsAlgClosure ℚ
  rw [hAlg] at h
  exact h

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (P : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom P u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)

/-- At a constructed original stage, every zero-obstruction class
relation for the actual descended trace coefficient extends along its
original free cover after the literal image-field transport. -/
theorem rationalTrace_exists_original_constructed_extension
    (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a,
      ∃ i : P →ₐ[ℚ] N.val,
      ∃ hi : ∀ x : P, (i x : AlgebraicClosure ℚ) = (x.val : AlgebraicClosure ℚ),
      let M := originalUnramifiedStageInUnion a N
      let hPM := originalUnramifiedStageInUnion_contains_embedded a P N i hi
      let B := rationalTraceOriginalFiniteRep a q σ M
        (finiteStageCoefficientKernel_mono (rationalArithmeticTraceZeroIntegerRep a q σ)
          P M hPM hker)
      let e := originalUnramifiedStageInUnionEquiv a N
      let BN := arithmeticOriginalStageRestrictedCoefficient (AlgebraicClosure ℚ) a M N
        e.symm.toAlgHom B
      let C := arithmeticOriginalStageClassRep (AlgebraicClosure ℚ) a ha N
      ∀ φ : originalRelationModule B ⟶
          arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha M,
        originalRelationExtensionObstruction B
          (arithmeticClassesModOutsideStageRep ℚ (AlgebraicClosure ℚ) a ha M) φ = 0 →
        ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C,
          originalRelationInclusion BN ≫ f =
            arithmeticOriginalStageRelationClassTransport (AlgebraicClosure ℚ) a ha M N
              e.symm.toAlgHom B φ := by
  letI : Finite (rationalTraceOriginalFiniteRep a q σ P hker) :=
    inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  have hB (b : rationalTraceOriginalFiniteRep a q σ P hker) : q • b = 0 := by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  obtain ⟨N, i, hi, hcriterion⟩ :=
    arithmeticClassStage_exists_original_constructed_relation_criterion
      (AlgebraicClosure ℚ) a ha P q hq2 hqa
      (rationalTraceOriginalFiniteRep a q σ P hker) hB
  refine ⟨N, i, hi, ?_⟩
  intro M hPM B e BN C φ hφ
  have hzero := arithmeticOriginalStageImage_relation_obstruction_zero
    (AlgebraicClosure ℚ) a ha N B φ hφ
  have hBN : BN = arithmeticOriginalStageRestrictedCoefficient (AlgebraicClosure ℚ) a P N i
      (rationalTraceOriginalFiniteRep a q σ P hker) :=
    rationalTraceOriginalStageImage_representation a q σ P hker N i hi
  let criterion (V : Rep.{0} ℤ Gal(N.val/ℚ)) :=
    ∀ χ : originalRelationModule V ⟶ C,
      originalRelationExtensionObstruction V C χ = 0 ↔
        ∃ f : Rep.free ℤ Gal(N.val/ℚ) V ⟶ C, originalRelationInclusion V ≫ f = χ
  have hc : criterion BN := (congrArg criterion hBN).mpr hcriterion
  exact (hc _).mp hzero

end
end Dubon2026

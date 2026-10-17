import Dubon2026.OriginalQuotientRelationFromFullOrder
import Dubon2026.OriginalArithmeticKernelNormTower
import Dubon2026.OriginalStageKernelCoefficientAction
import Dubon2026.ArithmeticClassesModOutsideH1

/-! # The constructed arithmetic stage realizes the relation criterion

The norm tower and actual coefficient restriction now feed the same
relation-extension theorem. Its only remaining class-field input is a
full-order original H2 element at the constructed enlarged stage. This
is the precise outstanding arithmetic premise on DUB-17's class/Ext,
reverse H1 localization, dual Selmer and patching dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Use the actual stage inclusion as the rational algebra throughout
the assembled field towers and coefficient restrictions. -/
local instance stageRelationRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- At a constructed stage above the original coefficient stage,
the actual zero-obstruction/extension equivalence follows from one
full-order original class. The norm roots, kernel action, support
unramifiedness and all comparison data are constructed. -/
theorem originalUnramifiedStage_exists_relation_criterion
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P.val/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      ∃ hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
        letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
        ∀ (u : groupCohomology (originalIdeleClassRep ℚ N.val) 2),
          addOrderOf u = Module.finrank ℚ N.val →
          ∀ χ : originalRelationModule BN ⟶ C,
            originalRelationExtensionObstruction BN C χ = 0 ↔
              ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = χ := by
  obtain ⟨E, N, hPE, hEN, hnorm⟩ :=
    originalUnramifiedStage_exists_kernel_norm_tower Ω a ha P p hp2 hpa
  letI : Algebra ℚ P.val := P.val.algebra'
  letI : Algebra ℚ E.val := E.val.algebra'
  letI : Algebra ℚ N.val := N.val.algebra'
  let hPN := hPE.trans hEN
  letI : Algebra P.val E.val := (IntermediateField.inclusion hPE).toRingHom.toAlgebra
  letI : Algebra E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
  letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ P.val E.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPE)
  letI : IsScalarTower ℚ E.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
  letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
    (originalIntegerMap_ne_zero (L := N.val) a ha)
  let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
  let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
  let H := (AlgEquiv.restrictNormalHom E.val : Gal(N.val/ℚ) →* Gal(E.val/ℚ)).ker
  letI : Fintype H := Fintype.ofFinite H
  have hunram (w : HeightOneSpectrum (𝓞 N.val)) (hw : w ∉ T) :
      Algebra.IsUnramifiedAt ℤ w.asIdeal := by
    have hwa : algebraMap (𝓞 ℚ) (𝓞 N.val) a ∉ w.asIdeal :=
      fun h => hw ((mem_originalExceptionalIntegerSupport _ _ _ w).mpr h)
    haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
      (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 ℚ) (p := w.asIdeal) w.ne_bot).mpr
        (N.property w hwa)
    haveI : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
      Algebra.FormallyUnramified.of_equiv
        (show ℤ ≃ₐ[ℤ] 𝓞 ℚ from { Rat.ringOfIntegersEquiv.symm with
          commutes' := fun r => map_intCast Rat.ringOfIntegersEquiv.symm r })
    exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime w.asIdeal)
  have hfix : ∀ g ∈ H, ∀ b : BN, BN.ρ g b = b := by
    intro g hg b
    exact originalFiniteGaloisStages_kernel_coefficient_trivial P.val E.val N.val hPE hEN B ⟨g, hg⟩ b
  refine ⟨N, hPN, ?_⟩
  dsimp only
  intro u hu χ
  exact originalClassQuotient_relation_extension_of_full_order ℚ N.val T hT hunram
    u hu p H hnorm.2 BN hB hfix χ

end
end Dubon2026

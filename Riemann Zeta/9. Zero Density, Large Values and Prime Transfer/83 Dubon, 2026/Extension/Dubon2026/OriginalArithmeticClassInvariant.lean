import Dubon2026.OriginalRationalFullOrderClass
import Dubon2026.OriginalClassH2InvariantFromGenerator
import Dubon2026.OriginalClassesModOutsideH2Comparison
import Dubon2026.ArithmeticClassesModOutsideH1

/-! # A constructed invariant for the actual arithmetic class coefficient

The mixed-degree full-order class and the literal outside-unit H2
isomorphism produce an injective invariant at every original stage.
This discharges the invariant input to DUB-17's finite relation pairing;
coherent tower normalization and completion comparisons remain separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Retain the original finite stage's displayed rational algebra. -/
local instance classInvariantRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- The original outside-unit class coefficient has a constructed injective
H2 invariant, with no prime-power restriction on the original field degree. -/
theorem originalUnramifiedStageClass_exists_injective_invariant
    {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (N : OriginalUnramifiedGaloisStage (Ω := Ω) a) :
    let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
      (originalIntegerMap_ne_zero (L := N.val) a ha)
    let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
    ∃ inv : groupCohomology (originalIdeleClassesModOutsideRep ℚ N.val T hT) 2 →+
      AddCircle (1 : ℚ), Function.Injective inv := by
  let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
    (originalIntegerMap_ne_zero (L := N.val) a ha)
  let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
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
  obtain ⟨u, hu⟩ := originalRationalNumberField_exists_full_order_class_of_algebra N.val
  obtain ⟨invG, hi, _, _, _⟩ := originalIdeleClass_exists_invariants_of_full_order ℚ N.val u hu
  let e := (originalClassesModOutsideH2Iso ℚ N.val T hT hunram).toLinearEquiv
  exact ⟨invG.comp e.symm.toLinearMap.toAddMonoidHom, hi.comp e.symm.injective⟩

end
end Dubon2026

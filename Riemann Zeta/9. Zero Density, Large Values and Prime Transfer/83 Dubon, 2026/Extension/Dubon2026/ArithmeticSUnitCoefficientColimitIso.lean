import Dubon2026.ArithmeticGlobalSourceColimits

/-! # Original arithmetic S-units as their actual equivariant coefficient colimit

The previously proved coefficient bijection respects the original arithmetic
Galois action. It identifies the ES term of the source colimit sequence with
the actual localized arithmetic S-units already used by the continuous H2
and integer Ext comparisons. No equivariant Ext vanishing is asserted.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The literal original finite-stage inclusions induce the actual equivariant ES comparison. -/
def arithmeticSUnitCoefficientColimitRepHom :
    arithmeticSUnitCoefficientColimitRep K Ω a ha ⟶ originalArithmeticSUnitRepresentation K Ω a ha :=
  Rep.ofHom {
    toLinearMap := arithmeticSUnitCoefficientColimitToGlobal K Ω a ha
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      obtain ⟨F, y, rfl⟩ := Module.DirectLimit.exists_of x
      change arithmeticSUnitCoefficientColimitToGlobal K Ω a ha
        (coefficientColimitAction (arithmeticGlobalSUnitStageRep K Ω a ha)
          (arithmeticGlobalSUnitStageTransition K Ω a ha) g
          (Module.DirectLimit.of ℤ
            (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
            (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
            (arithmeticSUnitCoefficientTransition K Ω a ha) F y)) =
        (originalArithmeticSUnitRepresentation K Ω a ha).ρ g
          (arithmeticSUnitCoefficientColimitToGlobal K Ω a ha
            (Module.DirectLimit.of ℤ
              (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
              (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
              (arithmeticSUnitCoefficientTransition K Ω a ha) F y))
      have hact : coefficientColimitAction (arithmeticGlobalSUnitStageRep K Ω a ha)
          (arithmeticGlobalSUnitStageTransition K Ω a ha) g
          (Module.DirectLimit.of ℤ
            (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
            (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
            (arithmeticSUnitCoefficientTransition K Ω a ha) F y) =
          Module.DirectLimit.of ℤ
            (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
            (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
            (arithmeticSUnitCoefficientTransition K Ω a ha) F
              ((arithmeticGlobalSUnitStageRep K Ω a ha F).ρ g y) :=
        coefficientColimitAction_of (arithmeticGlobalSUnitStageRep K Ω a ha)
          (arithmeticGlobalSUnitStageTransition K Ω a ha) g F y
      rw [hact]
      rw [arithmeticSUnitCoefficientColimitToGlobal_of K Ω a ha F,
        arithmeticSUnitCoefficientColimitToGlobal_of K Ω a ha F y]
      exact Rep.hom_comm_apply (arithmeticSUnitFiniteStageInclusion K Ω a ha F) g y }

/-- The actual equivariant comparison is bijective by original finite-stage S-unit descent and field injectivity. -/
theorem arithmeticSUnitCoefficientColimitRepHom_bijective :
    Function.Bijective (arithmeticSUnitCoefficientColimitRepHom K Ω a ha).hom :=
  ⟨arithmeticSUnitCoefficientColimitToGlobal_injective K Ω a ha,
    arithmeticSUnitCoefficientColimitToGlobal_surjective K Ω a ha⟩

/-- The original arithmetic S-unit representation is its literal finite-stage coefficient colimit. -/
def arithmeticSUnitCoefficientColimitIso :
    arithmeticSUnitCoefficientColimitRep K Ω a ha ≅ originalArithmeticSUnitRepresentation K Ω a ha := by
  haveI : Mono (arithmeticSUnitCoefficientColimitRepHom K Ω a ha) :=
    (Rep.mono_iff_injective _).mpr (arithmeticSUnitCoefficientColimitRepHom_bijective K Ω a ha).1
  haveI : Epi (arithmeticSUnitCoefficientColimitRepHom K Ω a ha) :=
    (Rep.epi_iff_surjective _).mpr (arithmeticSUnitCoefficientColimitRepHom_bijective K Ω a ha).2
  haveI : IsIso (arithmeticSUnitCoefficientColimitRepHom K Ω a ha) := isIso_of_mono_of_epi _
  exact asIso (arithmeticSUnitCoefficientColimitRepHom K Ω a ha)

/-- The equivariant identification uses the same original coefficient inclusion. -/
theorem arithmeticSUnitCoefficientColimitIso_hom :
    (arithmeticSUnitCoefficientColimitIso K Ω a ha).hom.hom.toLinearMap =
      arithmeticSUnitCoefficientColimitToGlobal K Ω a ha := rfl

end
end Dubon2026

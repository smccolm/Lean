import Dubon2026.GaloisSubgroupUnitCohomology
import Mathlib.RepresentationTheory.Invariants

/-! # Actual fixed-field units realize the normal quotient invariant coefficients -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Inclusion of original fixed-field units into the original invariant
coefficient representation, with its actual quotient Galois action. -/
def galoisNormalInvariantUnitInclusion :
    Rep.res (IsGalois.normalAutEquivQuotient S).toMonoidHom
        (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) ⟶
      (Rep.ofAlgebraAutOnUnits K L).quotientToInvariants S :=
  Rep.ofHom ⟨
    ((Units.map (algebraMap (IntermediateField.fixedField S) L).toMonoidHom).toAdditive.toIntLinearMap).codRestrict
      _ (by
        intro u s
        change s.val • Units.map (algebraMap (IntermediateField.fixedField S) L).toMonoidHom u.toMul =
          Units.map (algebraMap (IntermediateField.fixedField S) L).toMonoidHom u.toMul
        apply Units.ext
        exact u.toMul.val.property s),
    fun q => by
      apply LinearMap.ext
      intro u
      induction q using QuotientGroup.induction_on with
      | H g =>
        apply Subtype.ext
        change Units.map (algebraMap (IntermediateField.fixedField S) L).toMonoidHom
            ((IsGalois.normalAutEquivQuotient S (QuotientGroup.mk g)) •
              (Additive.toMul (Rep.toAdditive u) : (IntermediateField.fixedField S)ˣ)) =
          g • Units.map (algebraMap (IntermediateField.fixedField S) L).toMonoidHom
            (Additive.toMul (Rep.toAdditive u) : (IntermediateField.fixedField S)ˣ)
        apply Units.ext
        exact AlgEquiv.restrictNormalHom_apply (IntermediateField.fixedField S) g _ ⟩

/-- Literal fixed-field descent and the original unit inclusion are
mutually inverse on the actual invariant coefficients. -/
theorem galoisNormalInvariantUnitInclusion_bijective :
    Function.Bijective (galoisNormalInvariantUnitInclusion S).hom := by
  constructor
  · intro u v huv
    change u.toMul = v.toMul
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun x : (Rep.ofAlgebraAutOnUnits K L).quotientToInvariants S =>
      ((Additive.toMul (Rep.toAdditive x.val) : Lˣ) : L)) huv
  · intro x
    let ux : Lˣ := Additive.toMul (Rep.toAdditive x.val)
    let a : IntermediateField.fixedField S :=
      ⟨(ux : L), fun s =>
        congrArg (fun y : Rep.ofAlgebraAutOnUnits K L =>
          ((Additive.toMul (Rep.toAdditive y) : Lˣ) : L)) (x.property s)⟩
    have ha : a ≠ 0 := by
      intro h
      exact Units.ne_zero ux (congrArg (fun z : IntermediateField.fixedField S => (z : L)) h)
    refine ⟨Additive.ofMul (Units.mk0 a ha), ?_⟩
    apply Subtype.ext
    change Units.map (algebraMap (IntermediateField.fixedField S) L).toMonoidHom
      (Units.mk0 a ha) = ux
    apply Units.ext
    rfl

/-- The genuine fixed-field unit representation and the original normal
invariant representation are isomorphic under the actual quotient group. -/
def galoisNormalInvariantUnitCoefficientIso :
    Rep.res (IsGalois.normalAutEquivQuotient S).toMonoidHom
        (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) ≅
      (Rep.ofAlgebraAutOnUnits K L).quotientToInvariants S := by
  haveI : Mono (galoisNormalInvariantUnitInclusion S) :=
    (Rep.mono_iff_injective _).mpr (galoisNormalInvariantUnitInclusion_bijective S).1
  haveI : Epi (galoisNormalInvariantUnitInclusion S) :=
    (Rep.epi_iff_surjective _).mpr (galoisNormalInvariantUnitInclusion_bijective S).2
  haveI : IsIso (galoisNormalInvariantUnitInclusion S) := isIso_of_mono_of_epi _
  exact asIso (galoisNormalInvariantUnitInclusion S)

end
end Dubon2026

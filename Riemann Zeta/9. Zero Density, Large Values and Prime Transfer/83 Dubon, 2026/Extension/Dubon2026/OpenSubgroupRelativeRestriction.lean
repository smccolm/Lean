import Dubon2026.OpenSubgroupRelativeFixedFields

/-! # Literal finite relative restriction of original open Galois subgroups

Restriction onto the actual relative fixed-field automorphisms has exactly
the original smaller subgroup as kernel. This identifies the finite
quotient action needed to compare DUB-17's class-formation coefficients
and their normalized H2 maps without replacing the arithmetic subgroup.
-/

namespace Dubon2026
noncomputable section
open IntermediateField

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (U V : OpenSubgroup Gal(Ω/K)) (hVU : V.toSubgroup ≤ U.toSubgroup)
  [(V.toSubgroup.subgroupOf U.toSubgroup).Normal]

/-- Original restriction from the larger open subgroup to automorphisms of the genuine relative fixed field. -/
def openGaloisSubgroupRelativeRestriction :
    U →* Gal(IntermediateField.extendScalars (fixedField_le hVU) / fixedField U.toSubgroup) := by
  let T := IntermediateField.extendScalars (fixedField_le hVU)
  letI : IsGalois (fixedField U.toSubgroup) T :=
    openGaloisSubgroup_fixedField_relative_isGalois U V hVU
  exact (AlgEquiv.restrictNormalHom T).comp (openGaloisSubgroupFixedFieldEquiv U).toMonoidHom

/-- Relative restriction retains the original arithmetic automorphism on every actual fixed-field element. -/
theorem openGaloisSubgroupRelativeRestriction_apply
    (g : U) (x : IntermediateField.extendScalars (fixedField_le hVU)) :
    (openGaloisSubgroupRelativeRestriction U V hVU g x : Ω) = (g : Gal(Ω/K)) (x : Ω) := by
  let T := IntermediateField.extendScalars (fixedField_le hVU)
  letI : IsGalois (fixedField U.toSubgroup) T :=
    openGaloisSubgroup_fixedField_relative_isGalois U V hVU
  exact AlgEquiv.restrictNormal_commutes (openGaloisSubgroupFixedFieldEquiv U g) T x

/-- Every automorphism of the original relative fixed-field extension lifts to the original open subgroup. -/
theorem openGaloisSubgroupRelativeRestriction_surjective :
    Function.Surjective (openGaloisSubgroupRelativeRestriction U V hVU) := by
  let T := IntermediateField.extendScalars (fixedField_le hVU)
  letI : IsGalois (fixedField U.toSubgroup) T :=
    openGaloisSubgroup_fixedField_relative_isGalois U V hVU
  exact (AlgEquiv.restrictNormalHom_surjective Ω).comp (openGaloisSubgroupFixedFieldEquiv U).surjective

/-- The kernel of literal relative restriction is exactly the original smaller subgroup inside the larger one. -/
theorem openGaloisSubgroupRelativeRestriction_ker :
    (openGaloisSubgroupRelativeRestriction U V hVU).ker = V.toSubgroup.subgroupOf U.toSubgroup := by
  ext g
  constructor
  · intro hg
    change (g : Gal(Ω/K)) ∈ V.toSubgroup
    rw [← openGaloisSubgroup_fixing_fixedField V]
    apply (IntermediateField.mem_fixingSubgroup_iff (fixedField V.toSubgroup) _).mpr
    intro x hx
    have he := congrArg
      (fun f : Gal(IntermediateField.extendScalars (fixedField_le hVU) / fixedField U.toSubgroup) =>
        (f ⟨x, hx⟩ : Ω)) hg
    exact (openGaloisSubgroupRelativeRestriction_apply U V hVU g ⟨x, hx⟩).symm.trans he
  · intro hg
    change openGaloisSubgroupRelativeRestriction U V hVU g = 1
    ext x
    rw [openGaloisSubgroupRelativeRestriction_apply]
    exact x.property ⟨g.val, hg⟩

/-- The original quotient of open subgroups is the actual relative fixed-field Galois group. -/
def openGaloisSubgroupRelativeQuotientEquiv :
    U ⧸ V.toSubgroup.subgroupOf U.toSubgroup ≃*
      Gal(IntermediateField.extendScalars (fixedField_le hVU) / fixedField U.toSubgroup) :=
  QuotientGroup.liftEquiv _ (openGaloisSubgroupRelativeRestriction_surjective U V hVU)
    (openGaloisSubgroupRelativeRestriction_ker U V hVU).symm

/-- The quotient comparison is induced by the literal original relative restriction. -/
theorem openGaloisSubgroupRelativeQuotientEquiv_mk (g : U) :
    openGaloisSubgroupRelativeQuotientEquiv U V hVU g =
      openGaloisSubgroupRelativeRestriction U V hVU g := rfl

/-- The actual relative fixed-field degree equals the order of the original quotient of open subgroups. -/
theorem openGaloisSubgroupRelativeQuotient_degree :
    Nat.card (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup) =
      Module.finrank (fixedField U.toSubgroup)
        (IntermediateField.extendScalars (fixedField_le hVU)) := by
  let E := fixedField U.toSubgroup
  let T := IntermediateField.extendScalars (fixedField_le hVU)
  letI : Algebra K E := E.algebra'
  letI : Algebra K T := (fixedField V.toSubgroup).algebra'
  letI : IsScalarTower K E T := .of_algebraMap_eq' rfl
  letI : FiniteDimensional K T := openGaloisSubgroup_fixedField_finite V
  letI : FiniteDimensional E T := FiniteDimensional.right K E T
  letI : IsGalois E T := openGaloisSubgroup_fixedField_relative_isGalois U V hVU
  exact (Nat.card_congr (openGaloisSubgroupRelativeQuotientEquiv U V hVU).toEquiv).trans
    (IsGalois.card_aut_eq_finrank E T)

end
end Dubon2026

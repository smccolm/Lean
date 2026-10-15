import Dubon2026.ContinuousGaloisOpenSubgroupFinitePeriods

/-! # Original fixed fields and restriction for open arithmetic subgroups

The pinned infinite Galois correspondence and normal closure give finite
stages above an actual open subgroup's fixed field. Restriction is onto
the automorphisms fixing that field. These are the field inputs for the
open-subgroup class invariant comparison in DUB-17's class-formation route.
-/

namespace Dubon2026
noncomputable section
open IntermediateField

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- An original open Galois subgroup is exactly the fixing subgroup of its actual fixed field. -/
theorem openGaloisSubgroup_fixing_fixedField (H : OpenSubgroup Gal(Ω/K)) :
    (IntermediateField.fixedField H.toSubgroup).fixingSubgroup = H.toSubgroup :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨H.toSubgroup, H.isClosed⟩

/-- The actual fixed field of an open Galois subgroup is finite over the original base. -/
theorem openGaloisSubgroup_fixedField_finite (H : OpenSubgroup Gal(Ω/K)) :
    FiniteDimensional K (IntermediateField.fixedField H.toSubgroup) := by
  apply (InfiniteGalois.isOpen_iff_finite _).mp
  rw [openGaloisSubgroup_fixing_fixedField H]
  exact H.isOpen

/-- The original open subgroup consists of the actual automorphisms over its fixed field. -/
def openGaloisSubgroupFixedFieldEquiv (H : OpenSubgroup Gal(Ω/K)) :
    H ≃* Gal(Ω/IntermediateField.fixedField H.toSubgroup) :=
  (MulEquiv.subgroupCongr (openGaloisSubgroup_fixing_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv _)

/-- The fixed-field comparison retains every original field value. -/
theorem openGaloisSubgroupFixedFieldEquiv_apply
    (H : OpenSubgroup Gal(Ω/K)) (g : H) (x : Ω) :
    openGaloisSubgroupFixedFieldEquiv H g x = (g : Gal(Ω/K)) x := rfl

/-- There is an original finite Galois stage above both a prescribed stage and the open subgroup's fixed field. -/
theorem openGaloisSubgroup_exists_finite_stage
    (H : OpenSubgroup Gal(Ω/K)) (E : FiniteGaloisIntermediateField K Ω) :
    ∃ F : FiniteGaloisIntermediateField K Ω, E ≤ F ∧
      IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField := by
  let L := IntermediateField.fixedField H.toSubgroup
  letI : FiniteDimensional K L := openGaloisSubgroup_fixedField_finite H
  let W : FiniteGaloisIntermediateField K Ω := {
    toIntermediateField := normalClosure K L Ω
    finiteDimensional := normalClosure.is_finiteDimensional K L Ω
    isGalois := IsGalois.normalClosure K L Ω }
  exact ⟨E ⊔ W, le_sup_left, le_trans (IntermediateField.le_normalClosure L) le_sup_right⟩

/-- Fixed-field restriction and original base-field restriction have identical underlying automorphisms. -/
theorem openGaloisSubgroup_restriction_commutes
    (H : OpenSubgroup Gal(Ω/K)) (F : FiniteGaloisIntermediateField K Ω)
    (hF : IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField) :
    letI : Algebra (IntermediateField.fixedField H.toSubgroup) F :=
      (IntermediateField.inclusion hF).toAlgebra
    letI : IsScalarTower K (IntermediateField.fixedField H.toSubgroup) F :=
      .of_algebraMap_eq' rfl
    letI : IsGalois (IntermediateField.fixedField H.toSubgroup) F :=
      IsGalois.tower_top_of_isGalois K _ F
    letI : IsScalarTower (IntermediateField.fixedField H.toSubgroup) F Ω :=
      .of_algebraMap_eq' rfl
    ∀ g : H,
      ((openGaloisSubgroupFixedFieldEquiv H g).restrictNormal F).restrictScalars K =
        AlgEquiv.restrictNormalHom F (g : Gal(Ω/K)) := by
  let L := IntermediateField.fixedField H.toSubgroup
  letI : Algebra L F := (IntermediateField.inclusion hF).toAlgebra
  letI : IsScalarTower K L F := .of_algebraMap_eq' rfl
  letI : IsScalarTower L F Ω := .of_algebraMap_eq' rfl
  letI : IsGalois L F := IsGalois.tower_top_of_isGalois K L F
  intro g
  ext x
  change algebraMap F Ω ((openGaloisSubgroupFixedFieldEquiv H g).restrictNormal F x) = _
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormalHom_apply]
  rfl

/-- Every finite-stage automorphism over the actual fixed field lifts to the original open subgroup. -/
theorem openGaloisSubgroup_restriction_surjective
    (H : OpenSubgroup Gal(Ω/K)) (F : FiniteGaloisIntermediateField K Ω)
    (hF : IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField) :
    letI : Algebra (IntermediateField.fixedField H.toSubgroup) F :=
      (IntermediateField.inclusion hF).toAlgebra
    letI : IsScalarTower K (IntermediateField.fixedField H.toSubgroup) F :=
      .of_algebraMap_eq' rfl
    ∀ σ : Gal(F/IntermediateField.fixedField H.toSubgroup), ∃ g : H,
      AlgEquiv.restrictNormalHom F (g : Gal(Ω/K)) = σ.restrictScalars K := by
  let L := IntermediateField.fixedField H.toSubgroup
  letI : Algebra L F := (IntermediateField.inclusion hF).toAlgebra
  letI : IsScalarTower K L F := .of_algebraMap_eq' rfl
  letI : IsScalarTower L F Ω := .of_algebraMap_eq' rfl
  letI : IsGalois L F := IsGalois.tower_top_of_isGalois K L F
  intro σ
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective Ω σ
  let g := (openGaloisSubgroupFixedFieldEquiv H).symm τ
  refine ⟨g, ?_⟩
  ext x
  have he := congrArg (fun f : Gal(F/L) => (f x : Ω)) hτ
  change algebraMap F Ω (τ.restrictNormal F x) = (σ x : Ω) at he
  rw [AlgEquiv.restrictNormal_commutes] at he
  rw [AlgEquiv.restrictNormalHom_apply]
  rw [← openGaloisSubgroupFixedFieldEquiv_apply H g]
  simpa only [g, MulEquiv.apply_symm_apply] using he

end
end Dubon2026

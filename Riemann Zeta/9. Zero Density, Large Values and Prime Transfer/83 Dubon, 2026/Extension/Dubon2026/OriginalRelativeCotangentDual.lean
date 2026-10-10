import Dubon2026.OriginalResidueMaximalCotangent

/-! # The actual residue-field dual of the original relative maximal-ideal quotient -/

namespace Dubon2026

noncomputable section

variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Transport the genuine residue action on the actual relative maximal-ideal quotient through the original residue-field identification. -/
@[implicit_reducible]
def originalMaximalCotangentResidueModule
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Module (IsLocalRing.ResidueField O) (RelativeMaximalCotangent O R) :=
  Module.compHom (RelativeMaximalCotangent O R) eR.symm.toRingHom

/-- The transported residue-field action agrees with the original ring action under its true coefficient reduction. -/
theorem originalMaximalCotangent_reduction_smul
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (r : R) (x : RelativeMaximalCotangent O R) :
    (letI := originalMaximalCotangentResidueModule eR
     localCoefficientReduction eR r • x = r • x) := by
  letI := originalMaximalCotangentResidueModule eR
  change eR.symm (eR (IsLocalRing.residue R r)) • x = r • x
  rw [eR.symm_apply_apply, relativeMaximalCotangent_residue_smul]

/-- The ordinary linear dual over the original residue field of the literal relative maximal-ideal quotient. -/
abbrev OriginalRelativeMaximalCotangentDual
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :=
  letI := originalMaximalCotangentResidueModule eR
  RelativeMaximalCotangent O R →ₗ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O

/-- Original ring scaling on actual epsilon coefficients is multiplication by the genuine original residue. -/
theorem originalResidueEpsilon_snd_smul
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (r : R)
    (z : TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)) :
    (letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
     (r • z).val.snd = localCoefficientReduction eR r * z.val.snd) := by
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  change (TrivSqZeroExt.inl (localCoefficientReduction eR r) * z.val).snd = _
  simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul]

/-- The genuine epsilon-valued original-ring-linear maps give the ordinary residue-field-linear dual by their actual epsilon coefficients. -/
def originalMaximalCotangentToDual
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : OriginalResidueMaximalCotangentMaps eR) : OriginalRelativeMaximalCotangentDual eR := by
  letI := originalMaximalCotangentResidueModule eR
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  refine { toFun := fun x => (f x).val.snd, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    rw [map_add]
    rfl
  · intro k x
    obtain ⟨r, rfl⟩ := localCoefficientReduction_surjective eR k
    rw [originalMaximalCotangent_reduction_smul, map_smul]
    exact originalResidueEpsilon_snd_smul eR r (f x)

/-- The genuine ordinary residue dual lifts to actual epsilon-valued maps on the same literal quotient. -/
def originalMaximalCotangentFromDual
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : OriginalRelativeMaximalCotangentDual eR) : OriginalResidueMaximalCotangentMaps eR := by
  letI := originalMaximalCotangentResidueModule eR
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  refine
    { toFun := fun x => ⟨TrivSqZeroExt.inr (f x), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · exact (TrivSqZeroExt.mem_kerIdeal_iff_inr _ _ _).mpr rfl
  · intro x y
    apply Subtype.ext
    change TrivSqZeroExt.inr (f (x + y)) =
      TrivSqZeroExt.inr (f x) + TrivSqZeroExt.inr (f y)
    rw [map_add, TrivSqZeroExt.inr_add]
  · intro r x
    apply Subtype.ext
    change TrivSqZeroExt.inr (f (r • x)) =
      TrivSqZeroExt.inl (localCoefficientReduction eR r) * TrivSqZeroExt.inr (f x)
    rw [← originalMaximalCotangent_reduction_smul eR r x, map_smul,
      TrivSqZeroExt.inl_mul_inr]

/-- The actual epsilon-valued tangent maps and the usual dual of the literal relative maximal-ideal quotient are equivalent linearly over the original residue field. -/
def originalMaximalCotangentDualLinearEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    OriginalResidueMaximalCotangentMaps eR ≃ₗ[IsLocalRing.ResidueField O]
      OriginalRelativeMaximalCotangentDual eR := by
  letI := originalMaximalCotangentResidueModule eR
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  refine
    { toFun := originalMaximalCotangentToDual eR
      invFun := originalMaximalCotangentFromDual eR
      left_inv := by
        intro f
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact ((TrivSqZeroExt.mem_kerIdeal_iff_inr _ _ _).mp (f x).property).symm
      right_inv := by
        intro f
        apply LinearMap.ext
        intro x
        rfl
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        rfl
      map_smul' := by
        intro k f
        apply LinearMap.ext
        intro x
        rfl }

/-- The actual residue dual comparison records exactly the original epsilon coefficient on every genuine relative cotangent class. -/
theorem originalMaximalCotangentDualLinearEquiv_apply
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : OriginalResidueMaximalCotangentMaps eR) (x : RelativeMaximalCotangent O R) :
    originalMaximalCotangentDualLinearEquiv eR f x = (f x).val.snd := rfl

end
end Dubon2026

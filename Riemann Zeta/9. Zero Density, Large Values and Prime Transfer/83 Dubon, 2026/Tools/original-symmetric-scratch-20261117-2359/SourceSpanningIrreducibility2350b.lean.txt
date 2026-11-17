import Dubon2026.MatrixRepresentationBurnside

/-! DUB-17/18 -> original residual deformation inputs -> irreducibility from
full matrix spanning. Reuse the native simplicity of the endomorphism module. -/
namespace Dubon2026
noncomputable section
open Matrix

/-- A representation whose genuine group-algebra action is onto all linear
endomorphisms is irreducible. -/
theorem representation_irreducible_of_asAlgebraHom_surjective
    {G K V : Type} [Monoid G] [Field K] [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K G V) (h : Function.Surjective ρ.asAlgebraHom) :
    Representation.IsIrreducible ρ := by
  letI : AddCommGroup ρ.asModule := ρ.instAddCommGroupAsModule
  letI : AddCommMonoid ρ.asModule := ρ.instAddCommGroupAsModule.toAddCommMonoid
  letI : Module K ρ.asModule := ρ.instModuleAsModule
  letI : Module (MonoidAlgebra K G) ρ.asModule := ρ.instModuleMonoidAlgebraAsModule
  letI : RingHomSurjective ρ.asAlgebraHom.toRingHom := ⟨h⟩
  let e : ρ.asModule →ₛₗ[ρ.asAlgebraHom.toRingHom] V :=
    { ρ.asModuleEquiv.toAddHom with
      map_smul' := fun r v => ρ.asModuleEquiv_map_smul r v }
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (LinearMap.isSimpleModule_iff_of_bijective e ρ.asModuleEquiv.bijective).mpr inferInstance

/-- Full spanning by the actual representation matrices gives a surjective
original group-algebra action. -/
theorem matrixRepresentation_asAlgebraHom_surjective_of_span
    {G K ι : Type} [Group G] [Field K] [Fintype ι] [DecidableEq ι]
    (ρ : G →* GeneralLinearGroup ι K)
    (h : Submodule.span K (Set.range (fun g => (ρ g).val)) = ⊤) :
    Function.Surjective (matrixStandardRepresentation ρ).asAlgebraHom := by
  let r := matrixStandardRepresentation ρ
  let S := (LinearMap.range r.asAlgebraHom.toLinearMap).comap Matrix.toLin'.toLinearMap
  have hs : Submodule.span K (Set.range (fun g => (ρ g).val)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro M ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, by
      change r.asAlgebraHom (MonoidAlgebra.single g 1) = r g
      exact r.asAlgebraHom_single_one g⟩
  intro T
  obtain ⟨M, rfl⟩ := Matrix.toLin'.surjective T
  exact hs (by rw [h]; exact Submodule.mem_top) 

/-- The original matrix spanning conclusion discharges irreducibility of the
original representation without a change of coefficient field or basis. -/
theorem matrixRepresentation_irreducible_of_span
    {G K ι : Type} [Group G] [Field K] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ρ : G →* GeneralLinearGroup ι K)
    (h : Submodule.span K (Set.range (fun g => (ρ g).val)) = ⊤) :
    Representation.IsIrreducible (matrixStandardRepresentation ρ) :=
  representation_irreducible_of_asAlgebraHom_surjective _
    (matrixRepresentation_asAlgebraHom_surjective_of_span ρ h)

end
end Dubon2026

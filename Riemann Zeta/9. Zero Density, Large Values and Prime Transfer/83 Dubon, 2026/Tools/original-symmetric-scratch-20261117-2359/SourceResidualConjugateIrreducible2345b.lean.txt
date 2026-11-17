import Dubon2026.MatrixRepresentationSpanningDescent

/-! DUB-17/18 -> residual deformation inputs -> irreducibility in the original
coefficient coordinates. The finite-subfield witness supplies a conjugated
representation; native group-ring simplicity transports irreducibility across
that actual invertible basis change. -/
namespace Dubon2026
noncomputable section
open Matrix

/-- Equivalent actual representations have exactly the same irreducibility
property, by the native group-ring module equivalence. -/
theorem representation_irreducible_iff_of_equiv
    {G K V W : Type*} [Monoid G] [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (e : Representation.Equiv ρ σ) :
    Representation.IsIrreducible ρ ↔ Representation.IsIrreducible σ := by
  letI : AddCommGroup ρ.asModule := ρ.instAddCommGroupAsModule
  letI : AddCommMonoid ρ.asModule := ρ.instAddCommGroupAsModule.toAddCommMonoid
  letI : Module K ρ.asModule := ρ.instModuleAsModule
  letI : Module (MonoidAlgebra K G) ρ.asModule := ρ.instModuleMonoidAlgebraAsModule
  letI : AddCommGroup σ.asModule := σ.instAddCommGroupAsModule
  letI : AddCommMonoid σ.asModule := σ.instAddCommGroupAsModule.toAddCommMonoid
  letI : Module K σ.asModule := σ.instModuleAsModule
  letI : Module (MonoidAlgebra K G) σ.asModule := σ.instModuleMonoidAlgebraAsModule
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    Representation.irreducible_iff_isSimpleModule_asModule]
  exact LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.toLinearEquiv.bijective

/-- Literal conjugation of the original matrices preserves irreducibility. -/
theorem matrixRepresentation_irreducible_iff_conjugate
    {G K ι : Type} [Group G] [Field K] [Fintype ι] [DecidableEq ι]
    (ρ : G →* GeneralLinearGroup ι K) (B : GeneralLinearGroup ι K) :
    Representation.IsIrreducible (matrixStandardRepresentation ρ) ↔
      Representation.IsIrreducible (matrixStandardRepresentation
        ((MulEquiv.toMonoidHom (MulAut.conj B)).comp ρ)) := by
  let σ := (MulEquiv.toMonoidHom (MulAut.conj B)).comp ρ
  let e := (GeneralLinearGroup.toLin B).toLinearEquiv
  apply representation_irreducible_iff_of_equiv
  apply Representation.Equiv.mk e
  intro g
  have hm : B.val * (ρ g).val = (σ g).val * B.val := by
    change (B * ρ g).val = ((B * ρ g * B⁻¹) * B).val
    congr 1
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply LinearMap.ext
  intro v
  change B.val *ᵥ ((ρ g).val *ᵥ v) = (σ g).val *ᵥ (B.val *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]

end
end Dubon2026

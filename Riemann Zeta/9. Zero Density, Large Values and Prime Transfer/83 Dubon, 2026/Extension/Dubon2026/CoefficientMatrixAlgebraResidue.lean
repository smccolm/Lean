import Dubon2026.CoefficientRepresentationMatrixAlgebra
import Dubon2026.MatrixRepresentationSpanningDescent
import Dubon2026.LocalCoefficientReduction

/-! # Actual residue surjectivity of the original representation-generated matrix algebra -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Original residual absolute irreducibility and original coefficient constants make the genuine residue map from the actual representation-generated coefficient matrix algebra onto the full true residual matrix algebra surjective. -/
theorem coefficientRepresentationMatrixAlgebra_residue_surjective
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    Function.Surjective ((RingHom.mapMatrix (IsLocalRing.residue R)).comp
      (coefficientRepresentationMatrixAlgebra S ρ).val.toRingHom) := by
  classical
  have hconst : Function.Surjective (algebraMap O (IsLocalRing.ResidueField R)) := by
    intro y
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (eR y)
    refine ⟨o, eR.injective ?_⟩
    rw [eR.commutes]
    exact ho
  intro Y
  obtain ⟨t, a, ha⟩ := matrixRepresentation_exists_sum_of_extension (L := L)
    ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ) Y
  choose o ho using fun g => hconst (a g)
  let c : G → S := fun g => ⟨algebraMap O R (o g), S.algebraMap_mem (o g)⟩
  let X : Matrix ι ι R := ∑ g ∈ t, c g • (ρ g).val
  have hX : X ∈ coefficientRepresentationMatrixAlgebra S ρ := by
    apply (coefficientRepresentationMatrixAlgebra S ρ).toSubmodule.sum_mem
    intro g _
    exact (coefficientRepresentationMatrixAlgebra S ρ).toSubmodule.smul_mem _
      (Algebra.subset_adjoin ⟨g, rfl⟩)
  refine ⟨⟨X, hX⟩, ?_⟩
  ext i j
  have hy := congrArg (fun Z : Matrix ι ι (IsLocalRing.ResidueField R) => Z i j) ha
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hy
  change Y i j = ∑ g ∈ t, a g * IsLocalRing.residue R ((ρ g).val i j) at hy
  change IsLocalRing.residue R (X i j) = Y i j
  simp only [X, Matrix.sum_apply, Matrix.smul_apply]
  change IsLocalRing.residue R (∑ g ∈ t, algebraMap O R (o g) * (ρ g).val i j) = Y i j
  have ho' (g : G) : IsLocalRing.residue R (algebraMap O R (o g)) = a g := ho g
  rw [map_sum]
  simp only [map_mul, ho']
  exact hy.symm

end
end Dubon2026

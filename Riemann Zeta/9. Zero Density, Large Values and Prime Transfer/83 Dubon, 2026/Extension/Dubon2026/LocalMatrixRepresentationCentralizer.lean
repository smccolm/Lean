import Dubon2026.LocalMatrixRepresentationSpanning
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! # Scalar centralizers of actual local-ring lifts of absolutely irreducible residual representations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [IsLocalRing R] [Field L]
  [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]

omit [IsLocalRing R] in
/-- Commuting with a genuinely spanning original representation forces an original matrix to be scalar. -/
theorem matrixRepresentation_centralizer_scalar_of_span
    (ρ : G →* GeneralLinearGroup ι R)
    (hspan : Submodule.span R (Set.range (fun g => (ρ g).val)) = ⊤)
    (X : Matrix ι ι R) (hX : ∀ g, X * (ρ g).val = (ρ g).val * X) :
    ∃ a : R, X = Matrix.scalar ι a := by
  have hfull (Y : Matrix ι ι R) : X * Y = Y * X := by
    have hY : Y ∈ Submodule.span R (Set.range (fun g => (ρ g).val)) := by
      rw [hspan]
      trivial
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨g, rfl⟩ := hY
      exact hX g
    | zero => simp
    | add Y Z _ _ hY hZ => simp only [mul_add, add_mul, hY, hZ]
    | smul a Y _ hY => rw [Matrix.mul_smul, Matrix.smul_mul, hY]
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single
    (fun i j _ => (hfull (Matrix.single i j 1)).symm)
  exact ⟨a, ha.symm⟩

/-- Every original matrix commuting with an actual local-ring representation whose true residual representation is absolutely irreducible is an original scalar matrix. -/
theorem localMatrixRepresentation_centralizer_scalar
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))]
    (X : Matrix ι ι R) (hX : ∀ g, X * (ρ g).val = (ρ g).val * X) :
    ∃ a : R, X = Matrix.scalar ι a := by
  exact matrixRepresentation_centralizer_scalar_of_span ρ
    (localMatrixRepresentation_span_eq_top (L := L) ρ) X hX

omit [IsLocalRing R] in
/-- An actual invertible stabilizer of a genuinely spanning original representation is an original scalar unit. -/
theorem matrixRepresentation_stabilizer_scalar_unit_of_span
    (ρ : G →* GeneralLinearGroup ι R)
    (hspan : Submodule.span R (Set.range (fun g => (ρ g).val)) = ⊤)
    (U : GeneralLinearGroup ι R) (hU : ∀ g, U * ρ g = ρ g * U) :
    ∃ a : Rˣ, U = GeneralLinearGroup.scalar ι a := by
  obtain ⟨a, ha⟩ := matrixRepresentation_centralizer_scalar_of_span ρ hspan U.val
    (fun g => congrArg Units.val (hU g))
  have hcenter : U ∈ Subgroup.center (GeneralLinearGroup ι R) :=
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, ha.symm⟩
  rw [GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨a, ha⟩ := hcenter
  exact ⟨a, ha.symm⟩


/-- Every invertible change of basis stabilizing such an original local-ring representation is multiplication by an original coefficient unit. -/
theorem localMatrixRepresentation_stabilizer_scalar_unit
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))]
    (U : GeneralLinearGroup ι R) (hU : ∀ g, U * ρ g = ρ g * U) :
    ∃ a : Rˣ, U = GeneralLinearGroup.scalar ι a := by
  exact matrixRepresentation_stabilizer_scalar_unit_of_span ρ
    (localMatrixRepresentation_span_eq_top (L := L) ρ) U hU

end
end Dubon2026

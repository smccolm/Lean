import Dubon2026.SimpleModuleBurnside
import Dubon2026.MatrixAdjointSchur

/-! # Actual irreducible representation matrices span the full matrix algebra -/

namespace Dubon2026

noncomputable section

variable {G K V : Type} [Group G] [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The genuine original group-algebra action of an irreducible representation over an algebraically closed field attains every coefficient-linear endomorphism. -/
theorem irreducibleRepresentation_asAlgebraHom_surjective
    (ρ : Representation K G V) [Representation.IsIrreducible ρ] :
    Function.Surjective ρ.asAlgebraHom := by
  letI : AddCommGroup ρ.asModule := ρ.instAddCommGroupAsModule
  letI : AddCommMonoid ρ.asModule := ρ.instAddCommGroupAsModule.toAddCommMonoid
  letI : Module K ρ.asModule := ρ.instModuleAsModule
  letI : Module (MonoidAlgebra K G) ρ.asModule := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower K (MonoidAlgebra K G) ρ.asModule :=
    Representation.instIsScalarTowerMonoidAlgebraAsModule ρ
  letI : FiniteDimensional K ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
  letI : IsSimpleModule (MonoidAlgebra K G) ρ.asModule :=
    Representation.IsIrreducible.instIsSimpleModuleMonoidAlgebraAsModule
  exact @simpleModule_algebraAction_surjective K (MonoidAlgebra K G) ρ.asModule
    _ _ _ ρ.instAddCommGroupAsModule ρ.instModuleAsModule
    ρ.instModuleMonoidAlgebraAsModule _ _ _ _

end

noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K] [IsAlgClosed K]

/-- Every original matrix is an actual finite coefficient combination of the same irreducible representation's original matrices. -/
theorem irreducibleMatrixRepresentation_exists_sum
    (ρ : G →* GeneralLinearGroup ι K) [Representation.IsIrreducible (matrixStandardRepresentation ρ)]
    (X : Matrix ι ι K) :
    ∃ c : G →₀ K, X = c.sum (fun g a => a • (ρ g).val) := by
  obtain ⟨c, hc⟩ := irreducibleRepresentation_asAlgebraHom_surjective
    (matrixStandardRepresentation ρ) (Matrix.toLin' X)
  refine ⟨c, ?_⟩
  apply Matrix.toLin'.injective
  simpa only [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    map_sum, map_smul, matrixStandardRepresentation] using hc.symm

/-- Genuine irreducibility over an algebraically closed field makes the original representation matrices span the entire original matrix algebra. -/
theorem irreducibleMatrixRepresentation_span_eq_top
    (ρ : G →* GeneralLinearGroup ι K) [Representation.IsIrreducible (matrixStandardRepresentation ρ)] :
    Submodule.span K (Set.range (fun g => (ρ g).val)) = ⊤ := by
  apply top_unique
  intro X _
  obtain ⟨c, hc⟩ := irreducibleMatrixRepresentation_exists_sum ρ X
  rw [hc]
  change (∑ g ∈ c.support, c g • (ρ g).val) ∈ _
  apply Submodule.sum_mem
  intro g _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end
end Dubon2026

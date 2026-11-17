import Dubon2026.SourceSubfieldSymmetricAbsolute
import Dubon2026.SymmetricResidualRootLifts

/-! DUB-17/18 -> automorphy -> absolute residual symmetric-power irreducibility
on the cyclotomic kernel. The native perfect-subgroup lifting theorem retains
the embedded SL₂ image on that kernel, so the same three-operator proof applies. -/
namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- Restriction to the kernel of the original abelian character preserves
absolute symmetric-power irreducibility under the finite-subfield image bound. -/
theorem finiteSubfield_symmetric_kernel_absoluteIrreducible
    {G A K E L : Type} [Group G] [CommGroup A] [Field K] [Finite K]
    [Field E] [Field L] [Algebra E L] [NeZero (2 : K)] [NeZero (3 : K)]
    (q n : ℕ) [Fact q.Prime] [CharP K q]
    (θ : K →+* E) (hn : 2 * n < Nat.card K - 1) (hchar : n < q)
    (ρ : G →* GeneralLinearGroup (Fin 2) E) (χ : G →* A)
    (himage : ((GeneralLinearGroup.map θ).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := K))).range ≤ ρ.range) :
    Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) ((homogeneousSymmetricGL n).comp
        (ρ.comp χ.ker.subtype)))) := by
  apply finiteSubfield_symmetric_absoluteIrreducible q n θ hn hchar
  let ψ := (GeneralLinearGroup.map θ).comp (SpecialLinearGroup.toGL (n := Fin 2) (R := K))
  letI : Group.IsPerfect SL(2, K) := fieldSL2_isPerfect
  letI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hk := perfect_subgroup_le_map_character_kernel ρ χ ψ.range himage
  intro x hx
  obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp (hk hx)
  exact ⟨⟨g, hg⟩, hgx⟩

end
end Dubon2026

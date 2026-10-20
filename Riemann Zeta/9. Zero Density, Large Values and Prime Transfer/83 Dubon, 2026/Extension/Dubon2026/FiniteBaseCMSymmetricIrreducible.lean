import Dubon2026.FiniteBaseCMSymmetricMatrices
import Dubon2026.SymmetricResidualRootLifts
import Dubon2026.FiniteSymmetricAbsoluteIrreducible

/-! The original full residual SL2 image survives restriction to the actual
CM kernel. The existing perfect-subgroup character-kernel theorem and
finite symmetric-power irreducibility discharge a second irreducibility
assumption in DUB-17's polarized deformation comparison. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField MatrixGroups
noncomputable section

/-- Retain the original rational algebra in the CM irreducibility consumer. -/
local instance finiteBaseCMSymmetricIrreducibleUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K]
  {L : Type} [Field L] [Finite L] [TopologicalSpace L] [DiscreteTopology L]
  (q n : ℕ) [Fact q.Prime] [CharP L q]
  (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) L)
  (himage : (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := L)).range ≤ ρ.toMonoidHom.range)

include himage in
omit [Finite L] [Fact q.Prime] in
/-- The literal symmetric SL2 image remains in the original CM matrix restriction. -/
theorem finiteBaseCMSymmetricMatrices_image (hq : 3 < q) :
    ((homogeneousSymmetricGL (R := L) n).comp Matrix.SpecialLinearGroup.toGL).range ≤
      ((MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom).range := by
  letI : NeZero (2 : L) := ⟨by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((CharP.cast_eq_zero_iff L q 2).mp h)
    omega⟩
  letI : NeZero (3 : L) := ⟨by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 3) ((CharP.cast_eq_zero_iff L q 3).mp h)
    omega⟩
  let ψ := (homogeneousSymmetricGL (R := L) n).comp Matrix.SpecialLinearGroup.toGL
  let r := (homogeneousSymmetricGL (R := L) n).comp ρ.toMonoidHom
  have hi : ψ.range ≤ r.range := by
    rintro x ⟨s, rfl⟩
    obtain ⟨g, hg⟩ := himage (show Matrix.SpecialLinearGroup.toGL s ∈
      (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := L)).range from ⟨s, rfl⟩)
    exact ⟨g, congrArg (homogeneousSymmetricGL n) hg⟩
  letI : Group.IsPerfect SL(2, L) := fieldSL2_isPerfect
  letI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have h := perfect_subgroup_le_map_character_kernel r
    (finiteBaseQuadraticComponent a F K).toMonoidHom ψ.range hi
  intro x hx
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp (h hx)
  exact ⟨⟨g, hg⟩, he⟩

include himage in
/-- The actual CM symmetric-power matrices remain irreducible over every coefficient-field extension. -/
theorem finiteBaseCMSymmetricMatrices_absoluteIrreducible
    {E : Type} [Field E] [Algebra L E]
    (hq : 3 < q) (hn : 2 * n < Nat.card L - 1) (hchar : n < q) :
    Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := E)
        ((MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom))) :=
  finiteField_matrixRepresentation_absoluteIrreducible_of_symmetricSL2_image q n hn hchar _
    (finiteBaseCMSymmetricMatrices_image a F K q n ρ himage hq)

end
end Dubon2026

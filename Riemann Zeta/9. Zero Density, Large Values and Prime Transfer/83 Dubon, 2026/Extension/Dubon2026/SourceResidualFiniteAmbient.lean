import Dubon2026.SourceResidualLinearAlternatives
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! DUB-17/18 -> actual residual large image -> finite coefficient comparison.
The original finite coefficient image, the classified finite subfield and the
change-of-basis matrix all lie in one actual finite intermediate field. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
variable (p : ℕ) [Fact p.Prime]

/-- A finite set in the fixed algebraic closure lies in a finite intermediate field. -/
theorem exists_finite_intermediateField_containing (S : Set (K p)) (hS : S.Finite) :
    ∃ E : IntermediateField (ZMod p) (K p), Finite E ∧ S ⊆ E := by
  letI : Finite S := hS.to_subtype
  let E := IntermediateField.adjoin (ZMod p) S
  letI : FiniteDimensional (ZMod p) E :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  exact ⟨E, Module.finite_of_finite (ZMod p), IntermediateField.subset_adjoin _ _⟩

/-- The original coefficients, the image subfield and the actual conjugating matrix share a finite field. -/
theorem exists_residual_finite_matrix_ambient {F : Type*} [Field F] [Finite F]
    (j : F →+* K p) (m : ℕ) (A : GL (Fin 2) (K p)) :
    ∃ E : IntermediateField (ZMod p) (K p), Finite E ∧
      (∀ x : F, j x ∈ E) ∧
      (∀ x : GaloisField p m, galoisFieldRingHom (p := p) m x ∈ E) ∧
      ∀ i j : Fin 2, A.val i j ∈ E := by
  let S : Set (K p) := Set.range j ∪ Set.range (galoisFieldRingHom (p := p) m) ∪
    Set.range (fun ij : Fin 2 × Fin 2 => A.val ij.1 ij.2)
  have hS : S.Finite := ((Set.finite_range j).union (Set.finite_range _)).union
    (Set.finite_range _)
  obtain ⟨E, hE, hcontain⟩ := exists_finite_intermediateField_containing p S hS
  refine ⟨E, hE, ?_, ?_, ?_⟩
  · intro x
    exact hcontain (Or.inl (Or.inl ⟨x, rfl⟩))
  · intro x
    exact hcontain (Or.inl (Or.inr ⟨x, rfl⟩))
  · intro i j
    exact hcontain (Or.inr ⟨(i, j), rfl⟩)

/-- An invertible matrix whose entries lie in an intermediate field descends to that field. -/
theorem exists_matrix_over_intermediateField (E : IntermediateField (ZMod p) (K p))
    (A : GL (Fin 2) (K p)) (hA : ∀ i j, A.val i j ∈ E) :
    ∃ B : GL (Fin 2) E, GeneralLinearGroup.map E.subtype B = A := by
  let B : Matrix (Fin 2) (Fin 2) E := fun i j => ⟨A.val i j, hA i j⟩
  have hmap : B.map E.subtype = A.val := rfl
  have hdet : B.det ≠ 0 := by
    intro h
    rw [Matrix.det_fin_two] at h
    have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 0 :=
      congrArg (fun x : E => (x : K p)) h
    exact GeneralLinearGroup.det_ne_zero A (by simpa only [Matrix.det_fin_two] using hd)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero B hdet, ?_⟩
  apply Units.ext
  exact hmap

end
end Dubon2026.SourceDickson

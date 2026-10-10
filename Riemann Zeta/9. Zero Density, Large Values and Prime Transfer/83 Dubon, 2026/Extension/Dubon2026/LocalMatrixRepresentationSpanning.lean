import Dubon2026.MatrixRepresentationSpanningDescent
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama

/-! # Lifting genuine residual matrix spanning over the original local coefficient ring -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [IsLocalRing R]

omit [IsLocalRing R] in
/-- An original matrix whose entries lie in an ideal belongs to that ideal times the entire matrix module. -/
theorem matrix_mem_ideal_smul_top (I : Ideal R) (X : Matrix ι ι R)
    (hX : ∀ i j, X i j ∈ I) : X ∈ I • (⊤ : Submodule R (Matrix ι ι R)) := by
  rw [Matrix.matrix_eq_sum_single X]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  have h := Submodule.smul_mem_smul (hX i j)
    (show Matrix.single i j (1 : R) ∈ (⊤ : Submodule R (Matrix ι ι R)) from trivial)
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using h

/-- For an actual surjective coefficient reduction with maximal-ideal kernel, absolute irreducibility of the reduced original representation forces its original matrices to span the entire local-ring matrix algebra. -/
theorem localMatrixRepresentation_span_eq_top_of_reduction
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (r : R →+* K) (hr : Function.Surjective r)
    (hker : ∀ x, r x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map r).comp ρ)))] :
    Submodule.span R (Set.range (fun g => (ρ g).val)) = ⊤ := by
  classical
  let N := Submodule.span R (Set.range (fun g => (ρ g).val))
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro X _
  obtain ⟨s, a, ha⟩ := matrixRepresentation_exists_sum_of_extension (L := L)
    ((GeneralLinearGroup.map r).comp ρ)
    (X.map r)
  choose b hb using fun g => hr (a g)
  let Y : Matrix ι ι R := ∑ g ∈ s, b g • (ρ g).val
  have hY : Y ∈ N := by
    apply Submodule.sum_mem
    intro g _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  have hXY : X - Y ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Matrix ι ι R)) := by
    apply matrix_mem_ideal_smul_top
    intro i j
    apply (hker _).mp
    have h := congrArg (fun Z : Matrix ι ι K => Z i j) ha
    simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
    change r (X i j) =
      ∑ g ∈ s, a g * r ((ρ g).val i j) at h
    simp only [Matrix.sub_apply, Y, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, map_sum, map_mul, hb, h, sub_self]
  exact Submodule.mem_sup.mpr ⟨Y, hY, X - Y, hXY, by abel⟩


/-- If the actual residual representation becomes irreducible over an algebraically closed extension of its true residue field, the original representation matrices span the full matrix algebra over the original local coefficient ring. -/
theorem localMatrixRepresentation_span_eq_top
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] :
    Submodule.span R (Set.range (fun g => (ρ g).val)) = ⊤ := by
  exact localMatrixRepresentation_span_eq_top_of_reduction (L := L)
    (IsLocalRing.residue R) IsLocalRing.residue_surjective
    (IsLocalRing.residue_eq_zero_iff (R := R)) ρ

end
end Dubon2026

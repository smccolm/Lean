import Dubon2026.FullMatrixTracePairing
import Mathlib.Topology.Algebra.Algebra
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Instances.Matrix

/-! # Actual coordinate characterization and closedness of a matrix-basis span over a coefficient subalgebra -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {ι κ O R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing O] [CommRing R] [Algebra O R]

omit [Fintype ι] [DecidableEq ι] in
/-- The actual span of an original full matrix basis over a coefficient subalgebra consists exactly of matrices whose original basis coordinates belong to that same subalgebra. -/
theorem matrix_mem_subalgebra_basis_span_iff
    (S : Subalgebra O R) (b : Basis κ R (Matrix ι ι R)) (X : Matrix ι ι R) :
    X ∈ Submodule.span S (Set.range b) ↔ ∀ i, b.repr X i ∈ S := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨j, rfl⟩ := hY
      intro i
      simp only [Basis.repr_self_apply]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    | zero =>
      intro i
      simp only [map_zero, Finsupp.zero_apply]
      exact S.zero_mem
    | add Y Z _ _ hY hZ =>
      intro i
      simp only [map_add, Finsupp.add_apply]
      exact S.add_mem (hY i) (hZ i)
    | smul a Y _ hY =>
      intro i
      change b.repr ((a : R) • Y) i ∈ S
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact S.mul_mem a.property (hY i)
  · intro hX
    have hx : X = ∑ i, (⟨b.repr X i, hX i⟩ : S) • b i := (b.sum_repr X).symm
    rw [hx]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [Fintype κ] [DecidableEq κ] in
/-- Each genuine coordinate in a basis of the full original matrix algebra is continuous in the original coefficient topology, by its actual trace-dual matrix formula. -/
theorem matrixBasisCoordinate_continuous [TopologicalSpace R] [IsTopologicalRing R]
    (b : Basis κ R (Matrix ι ι R)) (i : κ) :
    Continuous (fun X : Matrix ι ι R => b.repr X i) := by
  let D : Matrix ι ι R := fullMatrixTraceDuality.symm (b.coord i)
  have hd : fullMatrixTracePairing D = b.coord i :=
    fullMatrixTraceDuality.apply_symm_apply (b.coord i)
  have hfun : (fun X : Matrix ι ι R => b.repr X i) =
      (fun X : Matrix ι ι R => Matrix.trace (D * X)) := by
    funext X
    exact (DFunLike.congr_fun hd X).symm
  rw [hfun]
  change Continuous (fun X : Matrix ι ι R => ∑ j, ∑ k, D j k * X k j)
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul ((continuous_apply j).comp (continuous_apply k))

/-- The original basis span over a closed coefficient subalgebra is closed in the original full matrix topology, as the common preimage of the actual closed coefficient algebra under its continuous basis coordinates. -/
theorem isClosed_matrix_subalgebra_basis_span [TopologicalSpace R] [IsTopologicalRing R]
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) (b : Basis κ R (Matrix ι ι R)) :
    IsClosed (Submodule.span S (Set.range b) : Set (Matrix ι ι R)) := by
  have hs : (Submodule.span S (Set.range b) : Set (Matrix ι ι R)) =
      ⋂ i, {X : Matrix ι ι R | b.repr X i ∈ S} := by
    ext X
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact matrix_mem_subalgebra_basis_span_iff S b X
  rw [hs]
  exact isClosed_iInter fun i => hS.preimage (matrixBasisCoordinate_continuous b i)

end
end Dubon2026

import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! DUB-17/18 -> original regular-prime local invariant dimensions ->
diagonalization over the original coefficient field. Distinct original
characteristic roots provide the eigenbasis using native eigenvector
independence; no scalar-extended cohomology or kernel comparison is needed. -/
namespace Dubon2026
noncomputable section
open Matrix Module

/-- Distinct original characteristic roots, one for each original matrix
coordinate, construct an eigenbasis over that same coefficient field. -/
theorem matrix_exists_original_eigenbasis_of_distinct_roots
    {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) (w : ι → F) (hw : Function.Injective w)
    (hroot : ∀ i, M.charpoly.IsRoot (w i)) :
    ∃ b : Basis ι F (ι → F), ∀ i, M.mulVec (b i) = w i • b i := by
  classical
  have he : ∀ i, Module.End.HasEigenvalue M.toLin' (w i) := by
    intro i
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    simpa only [Matrix.charpoly_toLin'] using hroot i
  choose v hv using fun i => (he i).exists_hasEigenvector
  have hi := Module.End.eigenvectors_linearIndependent' M.toLin' w hw v hv
  let b := basisOfLinearIndependentOfCardEqFinrank' v hi
    (Module.finrank_fintype_fun_eq_card F).symm
  refine ⟨b, ?_⟩
  intro i
  change M.toLin' (b i) = w i • b i
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using (hv i).apply_eq_smul

end
end Dubon2026

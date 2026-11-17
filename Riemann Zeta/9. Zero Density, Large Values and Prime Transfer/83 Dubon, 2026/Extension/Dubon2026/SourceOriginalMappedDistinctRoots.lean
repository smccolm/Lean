import Dubon2026.SourceOriginalDiagonalConjugacy

/-! DUB-17/18 -> original regular-prime invariant dimensions. Descend
specified original characteristic roots from a faithful coefficient map;
then construct the original diagonalization and fixed dimension. -/
namespace Dubon2026
noncomputable section
open Matrix

/-- A diagonalization after coefficient embedding proves each specified
original eigenvalue is a root of the original characteristic polynomial. -/
theorem original_characteristic_roots_of_mapped_diagonal
    {F E ι : Type} [Field F] [Field E] [Fintype ι] [DecidableEq ι]
    (j : F →+* E) (M : Matrix ι ι F) (w : ι → F)
    (C : GeneralLinearGroup ι E)
    (hC : C.val * M.map j * (C⁻¹).val = Matrix.diagonal (fun i => j (w i))) :
    ∀ i, M.charpoly.IsRoot (w i) := by
  intro i
  have hd : (Matrix.diagonal (fun k => j (w k))).charpoly.IsRoot (j (w i)) := by
    rw [Matrix.charpoly_diagonal, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [← hC, GeneralLinearGroup.coe_inv, Matrix.charpoly_units_conj, Matrix.charpoly_map] at hd
  exact hd.of_map j.injective

end
end Dubon2026

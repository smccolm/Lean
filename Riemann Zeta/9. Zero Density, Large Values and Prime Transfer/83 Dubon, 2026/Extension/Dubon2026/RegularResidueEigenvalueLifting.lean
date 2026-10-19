import Dubon2026.AdicCompleteResidueSplitting
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Lifting all distinct residual Frobenius eigenvalues

The auxiliary-prime local deformation rings needed for Dubon Theorem 2.6
require arbitrary symmetric-power rank. The existing native simple-root
theorem supplies every eigenvalue, without a domain assumption on the
coefficient ring. In particular it applies to local Artinian rings.
-/

namespace Dubon2026
noncomputable section
open Matrix Polynomial IsLocalRing

/-- Every distinct eigenvalue of an actual diagonal residual matrix lifts to a
root of the original characteristic polynomial in the same complete local ring. -/
theorem regularResidue_lift_eigenvalues
    {A ι : Type} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (α : ι → ResidueField A)
    (hM : M.map (residue A) = diagonal α) (hα : Function.Injective α) :
    ∃ l : ι → A, (∀ i, M.charpoly.IsRoot (l i)) ∧
      ∀ i, residue A (l i) = α i := by
  classical
  have hpoly : M.charpoly.map (residue A) = ∏ i, (X - C (α i)) := by
    rw [← charpoly_map, hM, charpoly_diagonal]
  have hs : (M.charpoly.map (residue A)).Separable := by
    rw [hpoly]
    exact separable_prod_X_sub_C_iff.mpr hα
  have hr (i : ι) : (M.charpoly.map (residue A)).IsRoot (α i) := by
    rw [hpoly, IsRoot.def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose l hl hres using fun i =>
    adicComplete_lift_separable_residue_root M.charpoly hs (α i) (hr i)
  exact ⟨l, hl, hres⟩

end
end Dubon2026

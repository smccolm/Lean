import Dubon2026.RegularResidueEigenvalueLifting
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Actual eigenvectors from characteristic-root adjugates

These columns give a strict diagonalizing basis for regular residual
Frobenius in the local deformation rings required by Dubon Theorem 2.6.
-/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

/-- The adjugate at an actual characteristic root has columns with the
corresponding eigenvalue, over any commutative coefficient ring. -/
theorem characteristicRoot_adjugate_eigenmatrix
    {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (a : A) (ha : M.charpoly.IsRoot a) :
    M * (scalar ι a - M).adjugate =
      scalar ι a * (scalar ι a - M).adjugate := by
  have hd : (scalar ι a - M).det = 0 := by
    rw [← eval_charpoly]
    exact ha
  have h := mul_adjugate (scalar ι a - M)
  rw [hd, zero_smul, sub_mul, sub_eq_zero] at h
  exact h.symm

/-- In a regular diagonal residual matrix the selected adjugate diagonal
entry is a unit; the remaining entries of its selected column reduce to zero. -/
theorem regularResidue_adjugate_column
    {A ι : Type} [CommRing A] [IsLocalRing A] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (α : ι → ResidueField A)
    (hM : M.map (residue A) = diagonal α) (hα : Function.Injective α)
    (i : ι) (a : A) (ha : residue A a = α i) :
    IsUnit ((scalar ι a - M).adjugate i i) ∧
      ∀ j, j ≠ i → residue A ((scalar ι a - M).adjugate j i) = 0 := by
  classical
  have hm : (residue A).mapMatrix (scalar ι a - M) =
      diagonal (fun j => α i - α j) := by
    rw [map_sub]
    change (scalar ι a).map (residue A) - M.map (residue A) = _
    rw [hM]
    ext j k
    by_cases h : j = k
    · subst k
      simp [ha]
    · simp [Matrix.scalar, h]
  have hadj : (residue A).mapMatrix (scalar ι a - M).adjugate =
      diagonal (fun j => ∏ k ∈ Finset.univ.erase j, (α i - α k)) := by
    rw [RingHom.map_adjugate, hm, adjugate_diagonal]
  constructor
  · apply (residue_ne_zero_iff_isUnit _).mp
    have he := congrArg (fun N : Matrix ι ι (ResidueField A) => N i i) hadj
    change residue A ((scalar ι a - M).adjugate i i) = _ at he
    simp only [diagonal_apply_eq] at he
    rw [he]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hj) (hα h).symm)
  · intro j hj
    have he := congrArg (fun N : Matrix ι ι (ResidueField A) => N j i) hadj
    change residue A ((scalar ι a - M).adjugate j i) = _ at he
    simpa only [diagonal_apply_ne _ hj] using he

end
end Dubon2026

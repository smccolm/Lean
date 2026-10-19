import Dubon2026.RegularResidueAdjugate
import Dubon2026.LocalCoefficientMatrixLifting

/-! # Strict diagonalization of actual regular residual Frobenius

The basis is constructed from normalized adjugate columns in arbitrary rank.
It serves the regular auxiliary-prime deformation rings on the dependency
chain to higher symmetric-power continuation for Dubon Theorem 2.6.
-/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

/-- A matrix with distinct diagonal residual eigenvalues has a diagonalizing
basis reducing to the identity, over the original complete local ring. -/
theorem regularResidue_strict_diagonalization
    {A ι : Type} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (α : ι → ResidueField A)
    (hM : M.map (residue A) = diagonal α) (hα : Function.Injective α) :
    ∃ (l : ι → A) (U : GeneralLinearGroup ι A),
      (∀ i, residue A (l i) = α i) ∧
      GeneralLinearGroup.map (residue A) U = 1 ∧
      M * U.val = U.val * diagonal l := by
  classical
  obtain ⟨l, hl, hres⟩ := regularResidue_lift_eigenvalues M α hM hα
  have hc (i : ι) := regularResidue_adjugate_column M α hM hα i (l i) (hres i)
  choose u hu using fun i => (hc i).1
  let V : Matrix ι ι A := fun j i =>
    (scalar ι (l i) - M).adjugate j i * ↑((u i)⁻¹)
  have hV : (residue A).mapMatrix V = 1 := by
    ext j i
    change residue A ((scalar ι (l i) - M).adjugate j i * ↑((u i)⁻¹)) =
      (1 : Matrix ι ι (ResidueField A)) j i
    by_cases h : j = i
    · subst j
      rw [← hu i]
      simp
    · rw [map_mul, (hc i).2 j h, zero_mul]
      simp [h]
  have hdet : IsUnit V.det := by
    apply isUnit_of_map_unit (residue A)
    rw [RingHom.map_det, hV, det_one]
    exact isUnit_one
  let U : GeneralLinearGroup ι A := GeneralLinearGroup.mk'' V hdet
  refine ⟨l, U, hres, ?_, ?_⟩
  · apply Units.ext
    exact hV
  · change M * V = V * diagonal l
    ext j i
    have he := congrArg (fun N : Matrix ι ι A => N j i)
      (characteristicRoot_adjugate_eigenmatrix M (l i) (hl i))
    simp only [scalar_apply, diagonal_mul] at he
    calc
      (M * V) j i = ((M * (scalar ι (l i) - M).adjugate) j i) * ↑((u i)⁻¹) := by
        simp only [mul_apply, V, Finset.sum_mul, mul_assoc]
      _ = (l i * (scalar ι (l i) - M).adjugate j i) * ↑((u i)⁻¹) := by
        exact congrArg (fun x : A => x * ↑((u i)⁻¹)) he
      _ = (V * diagonal l) j i := by
        rw [mul_diagonal]
        dsimp only [V]
        ring

end
end Dubon2026

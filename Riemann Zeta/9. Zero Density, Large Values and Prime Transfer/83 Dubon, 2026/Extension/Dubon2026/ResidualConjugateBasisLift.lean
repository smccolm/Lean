import Dubon2026.LocalCoefficientMatrixLifting
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Group.Conj

/-! The explicit split residual Frobenius basis lifts through the actual
coefficient residue map. This removes the diagonal-residual-basis hypothesis
from the tame character classification needed by Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

/-- A conjugacy to an explicit residual diagonal matrix supplies an actual
coefficient basis with that residual diagonal, using the genuine residue map. -/
theorem regularResidue_lift_conjugate_basis
    {A k ι : Type} [CommRing A] [IsLocalRing A] [Field k]
    [Fintype ι] [DecidableEq ι]
    (e : ResidueField A ≃+* k) (M : GeneralLinearGroup ι A)
    (D : GeneralLinearGroup ι k) (α : ι → k) (hD : D.val = diagonal α)
    (h : IsConj (GeneralLinearGroup.map (e.toRingHom.comp (residue A)) M) D) :
    ∃ V : GeneralLinearGroup ι A,
      (MulAut.conj V M).val.map (residue A) = diagonal (fun i => e.symm (α i)) := by
  let f := e.toRingHom.comp (residue A)
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  obtain ⟨V, hV⟩ := generalLinearGroup_map_surjective f
    (e.surjective.comp residue_surjective) c
  have hd : GeneralLinearGroup.map f (MulAut.conj V M) = D := by
    simpa only [MulAut.conj_apply, map_mul, map_inv, hV] using hc
  have he := congrArg (fun g : GeneralLinearGroup ι k => g.val) hd
  change (MulAut.conj V M).val.map f = D.val at he
  rw [hD] at he
  refine ⟨V, ?_⟩
  ext i j
  apply e.injective
  have hij := congrArg (fun X : Matrix ι ι k => X i j) he
  by_cases hij' : i = j
  · subst j
    simpa only [Matrix.map_apply, diagonal_apply_eq, RingEquiv.apply_symm_apply,
      f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe] using hij
  · simpa [Matrix.diagonal, hij', f] using hij

end
end Dubon2026

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Uniqueness of the labelled local characters in the auxiliary deformation
classification. This supplies injectivity for the character parameters of
the actual local deformation rings needed by Dubon Theorem 2.6. The native
distinct-diagonal centralizer theorem is over fields; here cancellation uses
units detected by the actual residue map, so Artinian coefficient rings work.
-/

namespace Dubon2026
open Matrix IsLocalRing

/-- A strict intertwiner between diagonal matrices preserves every labelled
diagonal entry, by cancellation of its diagonal units. -/
theorem regularResidue_diagonal_eq_of_strict_intertwiner
    {A ι : Type} [CommRing A] [IsLocalRing A] [Fintype ι] [DecidableEq ι]
    (l m : ι → A)
    (U : GeneralLinearGroup ι A) (hU : GeneralLinearGroup.map (residue A) U = 1)
    (h : diagonal l * U.val = U.val * diagonal m) :
    l = m := by
  have hdiag (i : ι) : IsUnit (U.val i i) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have he := congrArg (fun g : GeneralLinearGroup ι (ResidueField A) => g.val i i) hU
    have he' : residue A (U.val i i) = 1 := by simpa using he
    rw [he']
    exact one_ne_zero
  funext i
  have he := congrArg (fun X : Matrix ι ι A => X i i) h
  simp only [diagonal_mul, mul_diagonal] at he
  rw [mul_comm (U.val i i)] at he
  exact (hdiag i).mul_right_cancel he

/-- With distinct residual eigenvalues the strict intertwiner is itself
diagonal, identifying the remaining basis ambiguity in the local parameters. -/
theorem regularResidue_strict_intertwiner
    {A ι : Type} [CommRing A] [IsLocalRing A] [Fintype ι] [DecidableEq ι]
    (l m : ι → A) (hsep : Function.Injective (fun i => residue A (l i)))
    (U : GeneralLinearGroup ι A) (hU : GeneralLinearGroup.map (residue A) U = 1)
    (h : diagonal l * U.val = U.val * diagonal m) :
    l = m ∧ U.val = diagonal (fun i => U.val i i) := by
  have hlm := regularResidue_diagonal_eq_of_strict_intertwiner l m U hU h
  refine ⟨hlm, ?_⟩
  subst m
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · have he := congrArg (fun X : Matrix ι ι A => X i j) h
    simp only [diagonal_mul, mul_diagonal] at he
    have hu : IsUnit (l i - l j) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      rw [map_sub]
      exact sub_ne_zero.mpr (fun hh => hij (hsep hh))
    have hz : (l i - l j) * U.val i j = 0 := by
      rw [sub_mul, he, mul_comm (U.val i j), sub_self]
    have hz' : U.val i j = 0 := hu.mul_left_cancel (by simpa only [mul_zero] using hz)
    rw [hz', diagonal_apply_ne _ hij]

end Dubon2026

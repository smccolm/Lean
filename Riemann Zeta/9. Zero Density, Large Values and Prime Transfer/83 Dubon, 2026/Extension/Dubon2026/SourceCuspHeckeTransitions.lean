import Dubon2026.SourceCuspHeckeCosets
import Dubon2026.SourceIntegralHeckeConjugation

/-! Exact original Hecke transitions at the unit translation.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the Eisenstein exception -> cusp Hecke eigenvalue
ell+1. The existing original inverse transversal has one fixed exceptional
coset and one translation cycle; their conjugated transitions are computed here.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

variable (Q ell : ℕ) [NeZero ell] (hell : ell.Prime) (hellQ : Nat.Coprime ell Q)

/-- The original transition at the actual unit translation and original Hecke coset. -/
def sourceCuspHeckeTransition (i : Option (ZMod ell)) : heckeUpperSubgroup Q ell :=
  sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
    (sourceCuspHeckeRepresentative Q ell hell hellQ)
    (sourceCuspHeckeRepresentative_coset Q ell hell hellQ)
    (heckeUpperTranslation Q 1) (heckeUpperCosetEquiv hell hellQ i)

omit [NeZero ell] in
/-- The exceptional original transition is the actual conjugate by the Bezout matrix. -/
theorem sourceCuspHeckeTransition_none :
    (sourceCuspHeckeTransition Q ell hell hellQ none).val =
      heckeBezoutRepresentative ell Q hellQ * heckeUpperTranslation Q 1 *
        (heckeBezoutRepresentative ell Q hellQ)⁻¹ := by
  change (sourceCuspHeckeRepresentative Q ell hell hellQ
    (heckeUpperTranslation Q 1 • heckeUpperCoset ell Q hellQ none))⁻¹ *
      (heckeUpperTranslation Q 1 *
        sourceCuspHeckeRepresentative Q ell hell hellQ (heckeUpperCoset ell Q hellQ none)) = _
  rw [sourceCuspHeckeCoset_none]
  change (sourceCuspHeckeRepresentative Q ell hell hellQ
      (heckeUpperCosetEquiv hell hellQ none))⁻¹ *
    (heckeUpperTranslation Q 1 * sourceCuspHeckeRepresentative Q ell hell hellQ
      (heckeUpperCosetEquiv hell hellQ none)) = _
  rw [sourceCuspHeckeRepresentative_equiv]
  simp only [heckeUpperRepresentative, inv_inv, mul_assoc]

/-- The original cyclic transition is the literal translation by its integer carry. -/
theorem sourceCuspHeckeTransition_some (j : ZMod ell) :
    (sourceCuspHeckeTransition Q ell hell hellQ (some j)).val =
      heckeUpperTranslation Q (((j - 1).val : ℤ) + 1 - (j.val : ℤ)) := by
  change (sourceCuspHeckeRepresentative Q ell hell hellQ
    (heckeUpperTranslation Q 1 • heckeUpperCoset ell Q hellQ (some j)))⁻¹ *
      (heckeUpperTranslation Q 1 *
        sourceCuspHeckeRepresentative Q ell hell hellQ (heckeUpperCoset ell Q hellQ (some j))) = _
  rw [sourceCuspHeckeCoset_some]
  change (sourceCuspHeckeRepresentative Q ell hell hellQ
      (heckeUpperCosetEquiv hell hellQ (some (j - 1))))⁻¹ *
    (heckeUpperTranslation Q 1 * sourceCuspHeckeRepresentative Q ell hell hellQ
      (heckeUpperCosetEquiv hell hellQ (some j))) = _
  rw [sourceCuspHeckeRepresentative_equiv, sourceCuspHeckeRepresentative_equiv]
  apply Subtype.ext
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [heckeUpperRepresentative, heckeUpperTranslation, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
  ring

include hell in
/-- The actual integer carry is ell at zero and vanishes at every other residue. -/
theorem sourceCuspHeckeTranslation_carry (j : ZMod ell) :
    ((j - 1).val : ℤ) + 1 - (j.val : ℤ) = if j = 0 then (ell : ℤ) else 0 := by
  haveI : Fact (1 < ell) := ⟨hell.one_lt⟩
  by_cases hj : j = 0
  · subst j
    rw [if_pos rfl, zero_sub, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one, ZMod.val_zero]
    have := hell.one_lt
    omega
  · rw [if_neg hj]
    have hjv : 1 ≤ j.val := by
      have := (ZMod.val_eq_zero j).not.mpr hj
      omega
    have hv : (1 : ZMod ell).val ≤ j.val := by rwa [ZMod.val_one]
    rw [ZMod.val_sub hv, ZMod.val_one]
    omega

/-- The actual conjugated cyclic transitions are the unit translation at zero and identity elsewhere. -/
theorem sourceCuspHeckeConjugation_some (j : ZMod ell) :
    sourceHeckeConjugation hell (sourceCuspHeckeTransition Q ell hell hellQ (some j)) =
      if j = 0 then heckeUpperTranslation Q 1 else 1 := by
  rw [← sourceIntegralHeckeConjugate_eq_prime]
  have he := sourceCuspHeckeTransition_some Q ell hell hellQ j
  rw [sourceCuspHeckeTranslation_carry ell hell] at he
  apply Subtype.ext
  apply Subtype.ext
  change (!![_, _ / (ell : ℤ); _ * (ell : ℤ), _] :
    Matrix (Fin 2) (Fin 2) ℤ) = _
  simp only [he]
  split_ifs with hj
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [heckeUpperTranslation, Int.ediv_self (Int.natCast_ne_zero.mpr (NeZero.ne ell))]
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [heckeUpperTranslation]

end
end Dubon2026

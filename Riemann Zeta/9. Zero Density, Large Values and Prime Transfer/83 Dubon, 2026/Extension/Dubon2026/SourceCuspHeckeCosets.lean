import Dubon2026.SourceChosenCosetTraceOne
import Dubon2026.HeckeLowerCosets

/-! Original Hecke representatives for evaluation at the unit translation.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the Eisenstein exception -> actual cusp-evaluation
Hecke eigenvalue ell+1. The existing inverse representatives and their
proved complete transversal are retained, avoiding a second coset construction.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

variable (Q ell : ℕ) [NeZero ell] (hell : ell.Prime) (hellQ : Nat.Coprime ell Q)

/-- The existing actual inverse Hecke representatives, indexed by their original cosets. -/
def sourceCuspHeckeRepresentative (q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) : Gamma0 Q :=
  (heckeUpperRepresentative ell Q hellQ ((heckeUpperCosetEquiv hell hellQ).symm q))⁻¹

omit [NeZero ell] in
/-- The original chosen inverse representative has exactly its prescribed coset. -/
theorem sourceCuspHeckeRepresentative_coset (q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) :
    (sourceCuspHeckeRepresentative Q ell hell hellQ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) = q :=
  (heckeUpperCosetEquiv hell hellQ).apply_symm_apply q

omit [NeZero ell] in
/-- Reindexing by the proved original transversal recovers the actual inverse matrix. -/
theorem sourceCuspHeckeRepresentative_equiv (i : Option (ZMod ell)) :
    sourceCuspHeckeRepresentative Q ell hell hellQ (heckeUpperCosetEquiv hell hellQ i) =
      (heckeUpperRepresentative ell Q hellQ i)⁻¹ := by
  unfold sourceCuspHeckeRepresentative
  rw [Equiv.symm_apply_apply]

omit [NeZero ell] in
/-- The actual unit translation fixes the original exceptional Hecke coset. -/
theorem sourceCuspHeckeCoset_none :
    heckeUpperTranslation Q 1 • heckeUpperCoset ell Q hellQ none =
      heckeUpperCoset ell Q hellQ none := by
  change (QuotientGroup.mk
    (heckeUpperTranslation Q 1 * (heckeUpperRepresentative ell Q hellQ none)⁻¹) :
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell) = QuotientGroup.mk _
  rw [QuotientGroup.eq]
  change (((((heckeUpperTranslation Q 1 *
    (heckeUpperRepresentative ell Q hellQ none)⁻¹)⁻¹ *
      (heckeUpperRepresentative ell Q hellQ none)⁻¹).val 0 1 : ℤ) : ZMod ell)) = 0
  simp [heckeUpperRepresentative, heckeBezoutRepresentative, heckeUpperTranslation,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual unit translation decrements the original inverse-translation coset index. -/
theorem sourceCuspHeckeCoset_some (j : ZMod ell) :
    heckeUpperTranslation Q 1 • heckeUpperCoset ell Q hellQ (some j) =
      heckeUpperCoset ell Q hellQ (some (j - 1)) := by
  change (QuotientGroup.mk
    (heckeUpperTranslation Q 1 * (heckeUpperRepresentative ell Q hellQ (some j))⁻¹) :
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell) = QuotientGroup.mk _
  rw [QuotientGroup.eq]
  change (((((heckeUpperTranslation Q 1 *
    (heckeUpperRepresentative ell Q hellQ (some j))⁻¹)⁻¹ *
      (heckeUpperRepresentative ell Q hellQ (some (j - 1)))⁻¹).val 0 1 : ℤ) : ZMod ell)) = 0
  simp [heckeUpperRepresentative, heckeUpperTranslation,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

end
end Dubon2026

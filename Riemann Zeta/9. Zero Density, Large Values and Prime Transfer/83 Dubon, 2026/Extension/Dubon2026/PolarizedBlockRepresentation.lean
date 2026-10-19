import Dubon2026.PolarizedBlockMatrices

/-! A concrete matrix realization of the same disconnected polarized group.
This is the input for reusing the original framed coefficient rings in the
source-compatible CM deformation problem needed by DUB-17. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The component group acts by the original block-exchange matrix. -/
def polarizedComponentBlockRepresentation :
    Multiplicative (ZMod 2) →* GeneralLinearGroup (ι ⊕ ι) R where
  toFun z := if z.toAdd = 0 then 1 else polarizedBlockSwap
  map_one' := by simp
  map_mul' z w := by
    change (if z.toAdd + w.toAdd = (0 : ZMod 2) then 1 else polarizedBlockSwap) =
      (if z.toAdd = 0 then 1 else polarizedBlockSwap) *
        (if w.toAdd = 0 then 1 else polarizedBlockSwap)
    generalize z.toAdd = a
    generalize w.toAdd = b
    fin_cases a <;> fin_cases b
    · change (1 : GeneralLinearGroup (ι ⊕ ι) R) = 1 * 1
      exact (one_mul 1).symm
    · change polarizedBlockSwap = 1 * polarizedBlockSwap
      exact (one_mul _).symm
    · change polarizedBlockSwap = polarizedBlockSwap * 1
      exact (mul_one _).symm
    · change 1 = polarizedBlockSwap * polarizedBlockSwap
      rw [← pow_two, polarizedBlockSwap_sq]

/-- The two concrete matrix actions satisfy the original semidirect-product relation. -/
theorem polarizedBlockRepresentation_compatible (z : Multiplicative (ZMod 2)) :
    (polarizedIdentityBlockRepresentation (R := R) (ι := ι)).comp
        (polarizedSwitchAction z).toMonoidHom =
      (MulAut.conj (polarizedComponentBlockRepresentation z)).toMonoidHom.comp
        polarizedIdentityBlockRepresentation := by
  apply MonoidHom.ext
  intro x
  change polarizedIdentityBlockRepresentation
      ((if z.toAdd = 0 then (1 : MulAut (GeneralLinearGroup ι R × Rˣ))
        else polarizedSwitchAut) x) =
    (if z.toAdd = 0 then (1 : GeneralLinearGroup (ι ⊕ ι) R) else polarizedBlockSwap) *
      polarizedIdentityBlockRepresentation x *
      (if z.toAdd = 0 then (1 : GeneralLinearGroup (ι ⊕ ι) R) else polarizedBlockSwap)⁻¹
  split_ifs
  · simp
  · exact polarizedIdentityBlockRepresentation_switch x

/-- The source polarized target acts on the original space plus its twisted dual. -/
def polarizedBlockRepresentation :
    PolarizedGaloisGroup ι R →* GeneralLinearGroup (ι ⊕ ι) R :=
  SemidirectProduct.lift polarizedIdentityBlockRepresentation
    polarizedComponentBlockRepresentation polarizedBlockRepresentation_compatible

/-- The matrix realization retains its exact identity-component formula. -/
theorem polarizedBlockRepresentation_identity (x : GeneralLinearGroup ι R × Rˣ) :
    polarizedBlockRepresentation (polarizedIdentityComponent x) =
      polarizedBlockDiagonal x.1 (polarizedSwitch x).1 :=
  SemidirectProduct.lift_inl _ _ _ _

/-- The source involution is represented by the actual exchange matrix. -/
theorem polarizedBlockRepresentation_complexConjugation :
    polarizedBlockRepresentation (polarizedComplexConjugation (R := R) (ι := ι)) =
      polarizedBlockSwap := by
  change SemidirectProduct.lift _ _ _ (SemidirectProduct.inr _) = _
  rw [SemidirectProduct.lift_inr]
  change (if (1 : ZMod 2) = 0 then 1 else polarizedBlockSwap) = polarizedBlockSwap
  norm_num

/-- The exact matrix formula before splitting into the two connected components. -/
theorem polarizedBlockRepresentation_apply (x : PolarizedGaloisGroup ι R) :
    polarizedBlockRepresentation x =
      polarizedBlockDiagonal x.left.1 (polarizedSwitch x.left).1 *
        (if x.right.toAdd = 0 then 1 else polarizedBlockSwap) := rfl

end Dubon2026

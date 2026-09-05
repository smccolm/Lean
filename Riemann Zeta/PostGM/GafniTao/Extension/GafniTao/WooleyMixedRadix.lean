import GafniTao.WooleySection4Conditioned

/-!
# Mixed-radix residue classes for Wooley Section 4

The passage from a class modulo `q₁` and a class modulo `q₂` to a single
class modulo `q₂*q₁` is made explicit here.  For prime-power moduli this is
the correspondence `ζ = q₁*η+ξ` used between equations (4.13) and (4.14).
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The mixed-radix equivalence `(ξ,η) ↦ ξ+q₁η`. -/
def wooleyMixedRadixEquiv (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] :
    ZMod q₁ × ZMod q₂ ≃ ZMod (q₂ * q₁) :=
  (Equiv.prodComm (ZMod q₁) (ZMod q₂)).trans
    ((((ZMod.finEquiv q₂).symm.toEquiv).prodCongr
      ((ZMod.finEquiv q₁).symm.toEquiv)).trans
        (finProdFinEquiv.trans (ZMod.finEquiv (q₂ * q₁)).toEquiv))

@[simp] theorem wooleyMixedRadixEquiv_val
    (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (ξ : ZMod q₁) (η : ZMod q₂) :
    (wooleyMixedRadixEquiv q₁ q₂ (ξ, η)).val = ξ.val + q₁ * η.val := by
  cases q₁ with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q₁ =>
      cases q₂ with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q₂ => rfl

@[simp] theorem wooleyMixedRadixEquiv_apply
    (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (ξ : ZMod q₁) (η : ZMod q₂) :
    wooleyMixedRadixEquiv q₁ q₂ (ξ, η) =
      ((ξ.val + q₁ * η.val : ℕ) : ZMod (q₂ * q₁)) := by
  apply ZMod.val_injective (q₂ * q₁)
  rw [wooleyMixedRadixEquiv_val, ZMod.val_natCast_of_lt]
  calc
    ξ.val + q₁ * η.val < q₁ + q₁ * η.val :=
      Nat.add_lt_add_right ξ.val_lt _
    _ = q₁ * (η.val + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ q₁ * q₂ := Nat.mul_le_mul_left q₁ (Nat.succ_le_iff.mpr η.val_lt)
    _ = q₂ * q₁ := Nat.mul_comm _ _

/-- Reindex a double residue sum by the source correspondence
`ζ = q₁*η+ξ`. -/
theorem wooley_sum_mixedRadix
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {R : Type*} [AddCommMonoid R] (f : ZMod (q₂ * q₁) → R) :
    ∑ ξ : ZMod q₁, ∑ η : ZMod q₂,
        f (wooleyMixedRadixEquiv q₁ q₂ (ξ, η)) =
      ∑ ζ : ZMod (q₂ * q₁), f ζ := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (wooleyMixedRadixEquiv q₁ q₂) _ _ (fun _ => rfl)

#print axioms wooleyMixedRadixEquiv_val
#print axioms wooleyMixedRadixEquiv_apply
#print axioms wooley_sum_mixedRadix

end

end GafniTao

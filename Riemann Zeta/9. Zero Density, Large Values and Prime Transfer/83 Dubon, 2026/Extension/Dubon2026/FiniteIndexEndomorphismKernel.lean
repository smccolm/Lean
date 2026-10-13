import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! # Endomorphism index from a finite-index subgroup with trivial kernel

For the local power-index input to DUB-17, a sufficiently small unit subgroup
has injective power map. Its relative image index, multiplied by the actual
finite root kernel, determines the whole integer-unit power index.
-/

namespace Dubon2026
noncomputable section

variable {G : Type} [CommGroup G]

/-- An endomorphism's exact index is its kernel cardinality times its image
index inside any invariant finite-index subgroup on which it is injective. -/
theorem endomorphism_index_of_small_subgroup (f : G →* G) (U : Subgroup G)
    [U.FiniteIndex] (hstable : U.map f ≤ U) (hker : U ⊓ f.ker = ⊥) :
    f.range.index = Nat.card f.ker * (U.map f).relIndex U := by
  have hrel : U.relIndex (U ⊔ f.ker) = Nat.card f.ker := by
    rw [Subgroup.relIndex_sup_left, ← U.inf_relIndex_right f.ker, hker,
      Subgroup.relIndex_bot_left]
  have hindex := U.relIndex_mul_index (show U ≤ U ⊔ f.ker from le_sup_left)
  rw [hrel] at hindex
  have himage := (U.map f).relIndex_mul_index hstable
  rw [U.index_map f, ← hindex] at himage
  have hne : (U ⊔ f.ker).index ≠ 0 :=
    (Subgroup.finiteIndex_of_le (show U ≤ U ⊔ f.ker from le_sup_left)).index_ne_zero
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne)
  calc
    f.range.index * (U ⊔ f.ker).index = (U.map f).relIndex U *
        (Nat.card f.ker * (U ⊔ f.ker).index) := by
      simpa only [mul_comm] using himage.symm
    _ = (Nat.card f.ker * (U.map f).relIndex U) * (U ⊔ f.ker).index := by ac_rfl

end
end Dubon2026

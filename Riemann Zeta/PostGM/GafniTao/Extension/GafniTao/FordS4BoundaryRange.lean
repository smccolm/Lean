import GafniTao.FordS4ToS6

/-!
# Ford equation (3.5): the unique boundary value

The shifted residue interval has either `Q / p` or `Q / p + 1` elements.
Consequently every non-interior coordinate is the single endpoint `Q / p`.
These statements retain the floor convention used in the source.
-/

namespace GafniTao

noncomputable section

theorem ford_shiftedResidue_length_le_succ
    {Q p : ℕ} [NeZero p] (c : ZMod p) :
    (Q + fordNegativeResidue p c) / p ≤ Q / p + 1 := by
  have hp : 0 < p := NeZero.pos p
  rw [Nat.add_div hp]
  have ha : fordNegativeResidue p c / p = 0 :=
    Nat.div_eq_of_lt (fordNegativeResidue_lt c)
  rw [ha, add_zero]
  split <;> omega

theorem ford_shiftedResidueIndex_val_le
    {Q p : ℕ} [NeZero p] (c : ZMod p)
    (u : FordShiftedResidueIndex Q p c) :
    u.1 ≤ Q / p := by
  have hu := u.2
  have hlen := ford_shiftedResidue_length_le_succ (Q := Q) c
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hu hlen)

theorem ford_shiftedResidueIndex_not_interior_iff
    {Q p : ℕ} [NeZero p] (c : ZMod p)
    (u : FordShiftedResidueIndex Q p c) :
    ¬ u.1 < Q / p ↔ u.1 = Q / p := by
  constructor
  · intro hu
    exact Nat.le_antisymm (ford_shiftedResidueIndex_val_le c u)
      (Nat.le_of_not_gt hu)
  · intro hu
    omega

theorem ford_shiftedResidueIndex_boundary_unique
    {Q p : ℕ} [NeZero p] (c : ZMod p)
    {u v : FordShiftedResidueIndex Q p c}
    (hu : ¬ u.1 < Q / p) (hv : ¬ v.1 < Q / p) : u = v := by
  apply Fin.ext
  rw [(ford_shiftedResidueIndex_not_interior_iff c u).mp hu,
    (ford_shiftedResidueIndex_not_interior_iff c v).mp hv]

#print axioms ford_shiftedResidue_length_le_succ
#print axioms ford_shiftedResidueIndex_boundary_unique

end

end GafniTao

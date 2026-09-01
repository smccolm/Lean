import GafniTao.FordEquation34SourceS3

/-!
# Ford equation (3.5): exact residue-class parametrization

For a fixed class `c`, put `a = (-c).val`.  The integers `1 ≤ x ≤ Q`
with `x ≡ c (mod p)` are exactly `x = p*u-a` with
`1 ≤ u ≤ (Q+a)/p`.  This is the source sign convention in (3.5),
including the boundary truncation.
-/

namespace GafniTao

noncomputable section

def fordNegativeResidue (p : ℕ) (c : ZMod p) : ℕ := (-c).val

theorem fordNegativeResidue_lt {p : ℕ} [NeZero p] (c : ZMod p) :
    fordNegativeResidue p c < p :=
  ZMod.val_lt _

theorem ford_residue_add_negative_dvd
    {p x : ℕ} [NeZero p] (c : ZMod p) (hx : (x : ZMod p) = c) :
    p ∣ x + fordNegativeResidue p c := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [hx]
  change c + ((fordNegativeResidue p c : ℕ) : ZMod p) = 0
  rw [show ((fordNegativeResidue p c : ℕ) : ZMod p) = -c by
    exact ZMod.natCast_zmod_val (-c)]
  simp

theorem ford_shifted_residue_quotient_pos
    {p x : ℕ} [NeZero p] (c : ZMod p) (hxpos : 0 < x)
    (hx : (x : ZMod p) = c) :
    0 < (x + fordNegativeResidue p c) / p := by
  have hdvd := ford_residue_add_negative_dvd c hx
  have hp_le : p ≤ x + fordNegativeResidue p c :=
    Nat.le_of_dvd (by omega) hdvd
  exact (Nat.le_div_iff_mul_le (NeZero.pos p)).2 (by simpa using hp_le)

def FordShiftedResidueIndex (Q p : ℕ) (c : ZMod p) :=
  Fin ((Q + fordNegativeResidue p c) / p)

instance fordShiftedResidueIndexFinite
    (Q p : ℕ) (c : ZMod p) :
    Finite (FordShiftedResidueIndex Q p c) := by
  unfold FordShiftedResidueIndex
  infer_instance

noncomputable instance fordShiftedResidueIndexFintype
    (Q p : ℕ) (c : ZMod p) :
    Fintype (FordShiftedResidueIndex Q p c) := Fintype.ofFinite _

def fordResidueIntervalToShiftIndex
    {Q p : ℕ} [NeZero p] (c : ZMod p)
    (x : FordResidueInterval Q p c) : FordShiftedResidueIndex Q p c := by
  have hxpos : 0 < (x.1.1 + 1 : ℕ) := by omega
  have hu : 0 < ((x.1.1 + 1) + fordNegativeResidue p c) / p :=
    ford_shifted_residue_quotient_pos c hxpos x.2
  refine ⟨((x.1.1 + 1 + fordNegativeResidue p c) / p) - 1, ?_⟩
  have hxQ : x.1.1 + 1 ≤ Q := by exact x.1.2
  have hdiv : (x.1.1 + 1 + fordNegativeResidue p c) / p ≤
      (Q + fordNegativeResidue p c) / p :=
    Nat.div_le_div_right (Nat.add_le_add_right hxQ _)
  omega

def fordShiftIndexToResidueInterval
    {Q p : ℕ} [NeZero p] (c : ZMod p)
    (u : FordShiftedResidueIndex Q p c) : FordResidueInterval Q p c := by
  let a := fordNegativeResidue p c
  let x := p * (u.1 + 1) - a
  have ha : a < p := fordNegativeResidue_lt c
  have hpa : a < p * (u.1 + 1) := by
    have hu : 1 ≤ u.1 + 1 := by omega
    exact lt_of_lt_of_le ha (Nat.le_mul_of_pos_right p (by omega))
  have hmul : p * (u.1 + 1) ≤ Q + a := by
    have h := (Nat.le_div_iff_mul_le (NeZero.pos p)).mp u.2
    simpa [Nat.mul_comm] using h
  have hxpos : 0 < x := Nat.sub_pos_of_lt hpa
  have hxQ : x ≤ Q := by
    dsimp [x]
    omega
  refine ⟨⟨x - 1, by omega⟩, ?_⟩
  change (((x - 1 + 1 : ℕ) : ZMod p)) = c
  rw [Nat.sub_add_cancel (by omega : 1 ≤ x)]
  dsimp [x]
  rw [Nat.cast_sub (le_of_lt hpa), Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  simp only [ZMod.natCast_self, zero_mul, zero_sub]
  change -(((a : ℕ) : ZMod p)) = c
  rw [show ((a : ℕ) : ZMod p) = -c by
    exact ZMod.natCast_zmod_val (-c)]
  simp

theorem ford_shifted_residue_reconstruction
    {p x : ℕ} [NeZero p] (c : ZMod p) (hx : (x : ZMod p) = c) :
    p * ((x + fordNegativeResidue p c) / p) -
        fordNegativeResidue p c = x := by
  have hdvd := ford_residue_add_negative_dvd c hx
  rw [Nat.mul_div_cancel' hdvd]
  omega

def fordResidueShiftEquiv {Q p : ℕ} [NeZero p] (c : ZMod p) :
    FordResidueInterval Q p c ≃ FordShiftedResidueIndex Q p c where
  toFun := fordResidueIntervalToShiftIndex c
  invFun := fordShiftIndexToResidueInterval c
  left_inv x := by
    simp only [fordResidueIntervalToShiftIndex,
      fordShiftIndexToResidueInterval]
    apply Subtype.ext
    apply Fin.ext
    change (p * ((((x.1.1 + 1 + fordNegativeResidue p c) / p) - 1) + 1) -
        fordNegativeResidue p c) - 1 = x.1.1
    have hu := ford_shifted_residue_quotient_pos c (by omega : 0 < x.1.1 + 1) x.2
    rw [Nat.sub_add_cancel (by omega : 1 ≤
      (x.1.1 + 1 + fordNegativeResidue p c) / p)]
    rw [ford_shifted_residue_reconstruction c x.2]
    omega
  right_inv u := by
    simp only [fordResidueIntervalToShiftIndex,
      fordShiftIndexToResidueInterval]
    apply Fin.ext
    change ((p * (u.1 + 1) - fordNegativeResidue p c - 1 + 1 +
        fordNegativeResidue p c) / p) - 1 = u.1
    have ha : fordNegativeResidue p c < p * (u.1 + 1) := by
      exact lt_of_lt_of_le (fordNegativeResidue_lt c)
        (Nat.le_mul_of_pos_right p (by omega))
    rw [Nat.sub_add_cancel (by omega : 1 ≤
      p * (u.1 + 1) - fordNegativeResidue p c)]
    rw [Nat.sub_add_cancel (le_of_lt ha)]
    rw [Nat.mul_div_cancel_left (u.1 + 1) (NeZero.pos p)]
    omega

#print axioms fordResidueShiftEquiv

end

end GafniTao

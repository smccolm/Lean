import GafniTao.FordResidueShift

/-!
# Ford equation (3.5): shifted `S_4(c,p)` variables

The fixed residue-class variables are transported through the exact
`x = p*u-a` equivalence.  The resulting collision count is definitionally
the source equation (3.5), with `a=(-c).val` and its literal upper endpoint.
-/

namespace GafniTao

noncomputable section

abbrev FordS4ShiftedTuple (s Q p : ℕ) (c : ZMod p) :=
  Fin s → FordShiftedResidueIndex Q p c

def fordS4ShiftedMoment {k s Q p : ℕ} (q : ℕ) (c : ZMod p)
    (u : FordS4ShiftedTuple s Q p c) : Fin k → ℤ :=
  fun j => ∑ i : Fin s,
    (q : ℤ) ^ ((j : ℕ) + 1) *
      (((p * ((u i).1 + 1) - fordNegativeResidue p c : ℕ) : ℤ) ^
        ((j : ℕ) + 1))

def fordS4ResidueTupleToShifted
    {s Q p : ℕ} [NeZero p] (c : ZMod p)
    (x : FordS4ResidueTuple s Q p c) : FordS4ShiftedTuple s Q p c :=
  fun i => fordResidueIntervalToShiftIndex c (x i)

def fordS4ShiftedTupleToResidue
    {s Q p : ℕ} [NeZero p] (c : ZMod p)
    (u : FordS4ShiftedTuple s Q p c) : FordS4ResidueTuple s Q p c :=
  fun i => fordShiftIndexToResidueInterval c (u i)

theorem fordS4ShiftedTupleToResidue_leftInverse
    {s Q p : ℕ} [NeZero p] (c : ZMod p) :
    Function.LeftInverse
      (fordS4ResidueTupleToShifted (s := s) (Q := Q) c)
      (fordS4ShiftedTupleToResidue (s := s) (Q := Q) c) := by
  intro u
  funext i
  exact (fordResidueShiftEquiv c).apply_symm_apply (u i)

theorem fordS4ResidueTupleToShifted_leftInverse
    {s Q p : ℕ} [NeZero p] (c : ZMod p) :
    Function.LeftInverse
      (fordS4ShiftedTupleToResidue (s := s) (Q := Q) c)
      (fordS4ResidueTupleToShifted (s := s) (Q := Q) c) := by
  intro x
  funext i
  exact (fordResidueShiftEquiv c).symm_apply_apply (x i)

@[simp] theorem fordShiftIndexToResidueInterval_value
    {Q p : ℕ} [NeZero p] (c : ZMod p)
    (u : FordShiftedResidueIndex Q p c) :
    (fordShiftIndexToResidueInterval c u).1.1 + 1 =
      p * (u.1 + 1) - fordNegativeResidue p c := by
  simp only [fordShiftIndexToResidueInterval]
  have ha : fordNegativeResidue p c < p * (u.1 + 1) :=
    lt_of_lt_of_le (fordNegativeResidue_lt c)
      (Nat.le_mul_of_pos_right p (by omega))
  omega

theorem fordS4ResidueMoment_shifted
    {k s Q p : ℕ} [NeZero p] (q : ℕ) (c : ZMod p)
    (u : FordS4ShiftedTuple s Q p c) :
    fordS4ResidueMoment (k := k) q c
        (fordS4ShiftedTupleToResidue c u) =
      fordS4ShiftedMoment (k := k) q c u := by
  ext j
  simp [fordS4ResidueMoment, fordS4ShiftedMoment,
    fordS4ShiftedTupleToResidue,
    fordShiftIndexToResidueInterval_value, Nat.cast_pow, Nat.cast_mul]

def fordS4ShiftedCount
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) : ℕ :=
  Nat.card (FordCharacterCollision
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fordS4ShiftedMoment (k := k) q c :
      FordS4ShiftedTuple s Q p c → Fin k → ℤ))

def fordS4CollisionToShifted
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p)
    (u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ResidueMoment (k := k) q c :
        FordS4ResidueTuple s Q p c → Fin k → ℤ)) :
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ShiftedMoment (k := k) q c :
        FordS4ShiftedTuple s Q p c → Fin k → ℤ) := by
  let x := fordS4ResidueTupleToShifted c u.1.1.2
  let y := fordS4ResidueTupleToShifted c u.1.2.2
  refine ⟨((u.1.1.1, x), (u.1.2.1, y)), ?_⟩
  change _ + fordS4ShiftedMoment (k := k) q c x =
    _ + fordS4ShiftedMoment (k := k) q c y
  rw [← fordS4ResidueMoment_shifted, ← fordS4ResidueMoment_shifted]
  rw [fordS4ResidueTupleToShifted_leftInverse,
    fordS4ResidueTupleToShifted_leftInverse]
  simpa only [x, y] using u.2

def fordS4ShiftedCollisionToResidue
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p)
    (u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ShiftedMoment (k := k) q c :
        FordS4ShiftedTuple s Q p c → Fin k → ℤ)) :
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ResidueMoment (k := k) q c :
        FordS4ResidueTuple s Q p c → Fin k → ℤ) := by
  refine ⟨((u.1.1.1, fordS4ShiftedTupleToResidue c u.1.1.2),
      (u.1.2.1, fordS4ShiftedTupleToResidue c u.1.2.2)), ?_⟩
  rw [fordS4ResidueMoment_shifted, fordS4ResidueMoment_shifted]
  exact u.2

def fordS4CollisionShiftEquiv
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) :
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ResidueMoment (k := k) q c :
        FordS4ResidueTuple s Q p c → Fin k → ℤ) ≃
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ShiftedMoment (k := k) q c :
        FordS4ShiftedTuple s Q p c → Fin k → ℤ) where
  toFun := fordS4CollisionToShifted Ψ hdk c
  invFun := fordS4ShiftedCollisionToResidue Ψ hdk c
  left_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact fordS4ResidueTupleToShifted_leftInverse c u.1.1.2
    · apply Prod.ext
      · rfl
      · exact fordS4ResidueTupleToShifted_leftInverse c u.1.2.2
  right_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact fordS4ShiftedTupleToResidue_leftInverse c u.1.1.2
    · apply Prod.ext
      · rfl
      · exact fordS4ShiftedTupleToResidue_leftInverse c u.1.2.2

theorem fordS4Count_eq_shiftedCount
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) :
    fordS4Count (P := P) Ψ hdk s Q q c =
      fordS4ShiftedCount (P := P) Ψ hdk s Q q c := by
  exact Nat.card_congr (fordS4CollisionShiftEquiv Ψ hdk c)

#print axioms fordS4Count_eq_shiftedCount

end

end GafniTao

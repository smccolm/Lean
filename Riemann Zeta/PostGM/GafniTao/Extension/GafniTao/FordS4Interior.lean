import GafniTao.FordS4Shifted

/-!
# Ford equation (3.5): exact interior/boundary split

The shifted range has length `floor ((Q+a)/p)`, while the source interior
has length `floor (Q/p)`.  This file constructs the literal inclusion and
separates the `S_4` collision type into its interior `S_6` precursor and the
boundary set `S_5`.
-/

namespace GafniTao

noncomputable section

def fordInteriorToShiftIndex
    {Q p : ℕ} [NeZero p] (c : ZMod p) (u : Fin (Q / p)) :
    FordShiftedResidueIndex Q p c := by
  refine ⟨u.1, lt_of_lt_of_le u.2 ?_⟩
  exact Nat.div_le_div_right (Nat.le_add_right Q (fordNegativeResidue p c))

theorem fordInteriorToShiftIndex_injective
    {Q p : ℕ} [NeZero p] (c : ZMod p) :
    Function.Injective (fordInteriorToShiftIndex (Q := Q) c) := by
  intro u v h
  have hv : (fordInteriorToShiftIndex c u).1 =
      (fordInteriorToShiftIndex c v).1 :=
    congrArg (fun w : FordShiftedResidueIndex Q p c => w.1) h
  exact Fin.ext hv

abbrev FordS4InteriorTuple (s Q p : ℕ) := FordBox s (Q / p)

def fordS4InteriorTupleToShifted
    {s Q p : ℕ} [NeZero p] (c : ZMod p)
    (u : FordS4InteriorTuple s Q p) : FordS4ShiftedTuple s Q p c :=
  fun i => fordInteriorToShiftIndex c (u i)

theorem fordS4InteriorTupleToShifted_injective
    {s Q p : ℕ} [NeZero p] (c : ZMod p) :
    Function.Injective (fordS4InteriorTupleToShifted (s := s) (Q := Q) c) := by
  intro u v h
  funext i
  exact fordInteriorToShiftIndex_injective (Q := Q) c (congrFun h i)

def fordS4InteriorMoment {k s Q p : ℕ} [NeZero p]
    (q : ℕ) (c : ZMod p) (u : FordS4InteriorTuple s Q p) : Fin k → ℤ :=
  fordS4ShiftedMoment q c (fordS4InteriorTupleToShifted c u)

def fordS4InteriorCount
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) : ℕ :=
  Nat.card (FordCharacterCollision
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fordS4InteriorMoment (k := k) q c :
      FordS4InteriorTuple s Q p → Fin k → ℤ))

def FordS4ShiftedInterior
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) :=
  {u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ShiftedMoment (k := k) q c :
        FordS4ShiftedTuple s Q p c → Fin k → ℤ) //
    (∀ i : Fin s, (u.1.1.2 i).1 < Q / p) ∧
      (∀ i : Fin s, (u.1.2.2 i).1 < Q / p)}

def FordS4ShiftedBoundary
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) :=
  {u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ShiftedMoment (k := k) q c :
        FordS4ShiftedTuple s Q p c → Fin k → ℤ) //
    ¬ ((∀ i : Fin s, (u.1.1.2 i).1 < Q / p) ∧
      (∀ i : Fin s, (u.1.2.2 i).1 < Q / p))}

def fordS4InteriorCollisionToShifted
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p)
    (u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4InteriorMoment (k := k) q c :
        FordS4InteriorTuple s Q p → Fin k → ℤ)) :
    FordS4ShiftedInterior (P := P) Ψ hdk s Q q c := by
  refine ⟨⟨((u.1.1.1, fordS4InteriorTupleToShifted c u.1.1.2),
      (u.1.2.1, fordS4InteriorTupleToShifted c u.1.2.2)), u.2⟩, ?_⟩
  constructor
  · intro i
    simpa only [fordS4InteriorTupleToShifted,
      fordInteriorToShiftIndex] using (u.1.1.2 i).2
  · intro i
    simpa only [fordS4InteriorTupleToShifted,
      fordInteriorToShiftIndex] using (u.1.2.2 i).2

def fordShiftedInteriorTupleToInterior
    {s Q p : ℕ} [NeZero p] {c : ZMod p}
    (u : FordS4ShiftedTuple s Q p c)
    (hu : ∀ i : Fin s, (u i).1 < Q / p) : FordS4InteriorTuple s Q p :=
  fun i => ⟨(u i).1, hu i⟩

def fordS4ShiftedInteriorToCollision
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (u : FordS4ShiftedInterior (P := P) Ψ hdk s Q q c) :
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4InteriorMoment (k := k) q c :
        FordS4InteriorTuple s Q p → Fin k → ℤ) := by
  let x := fordShiftedInteriorTupleToInterior (s := s) (Q := Q) (p := p)
    (c := c) (u.val.val.1.2 : FordS4ShiftedTuple s Q p c) u.property.1
  let y := fordShiftedInteriorTupleToInterior (s := s) (Q := Q) (p := p)
    (c := c) (u.val.val.2.2 : FordS4ShiftedTuple s Q p c) u.property.2
  refine ⟨((u.val.val.1.1, x), (u.val.val.2.1, y)), ?_⟩
  change _ + fordS4InteriorMoment (k := k) q c x =
    _ + fordS4InteriorMoment (k := k) q c y
  simpa [fordS4InteriorMoment, fordS4InteriorTupleToShifted,
    fordShiftedInteriorTupleToInterior, fordInteriorToShiftIndex,
    x, y] using u.val.property

def fordS4InteriorCollisionEquiv
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) :
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4InteriorMoment (k := k) q c :
        FordS4InteriorTuple s Q p → Fin k → ℤ) ≃
      FordS4ShiftedInterior (P := P) Ψ hdk s Q q c where
  toFun := fordS4InteriorCollisionToShifted Ψ hdk c
  invFun := fordS4ShiftedInteriorToCollision Ψ hdk c
  left_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        apply Fin.ext
        rfl
    · apply Prod.ext
      · rfl
      · funext i
        apply Fin.ext
        rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        apply Fin.ext
        rfl
    · apply Prod.ext
      · rfl
      · funext i
        apply Fin.ext
        rfl

theorem fordS4InteriorCount_eq_shiftedInterior
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) :
    fordS4InteriorCount (P := P) Ψ hdk s Q q c =
      Nat.card (FordS4ShiftedInterior (P := P) Ψ hdk s Q q c) := by
  exact Nat.card_congr (fordS4InteriorCollisionEquiv Ψ hdk c)

theorem fordS4Shifted_card_eq_interior_add_boundary
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) :
    fordS4ShiftedCount (P := P) Ψ hdk s Q q c =
      Nat.card (FordS4ShiftedInterior (P := P) Ψ hdk s Q q c) +
        Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) := by
  let U := FordCharacterCollision
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fordS4ShiftedMoment (k := k) q c :
      FordS4ShiftedTuple s Q p c → Fin k → ℤ)
  let good : U → Prop := fun u =>
    (∀ i : Fin s, (u.1.1.2 i).1 < Q / p) ∧
      (∀ i : Fin s, (u.1.2.2 i).1 < Q / p)
  change Nat.card U = Nat.card {u : U // good u} +
    Nat.card {u : U // ¬ good u}
  letI : Finite U := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype U := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  exact (Nat.add_sub_of_le (Fintype.card_subtype_le good)).symm

#print axioms fordS4Shifted_card_eq_interior_add_boundary

end

end GafniTao

import GafniTao.FordHolderInterpolation

/-!
# Ford Lemma 3.2: the diagonal lower bound for `S₄`

This file keeps the zeroth residue moment as the actual collision count of
the polynomial Weyl sum.  Pairing every such polynomial collision with one
common interior residue tuple gives the source lower bound for `S₄`.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

def fordPolynomialCollisionCount
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) : ℕ :=
  Nat.card (FordCharacterCollision
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fun _ : Fin 1 ↦ (0 : Fin k → ℤ)))

theorem fordPolynomialFourier_eq_collisionCount
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) :
    ∫ α : UnitAddTorus (Fin k),
        ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2
        ∂fordTorusMeasure k =
      (fordPolynomialCollisionCount (P := P) (p := p) Ψ hdk : ℝ) := by
  have h := ford_character_collision_mean_eq
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fun _ : Fin 1 ↦ (0 : Fin k → ℤ))
  simpa [fordPolynomialCollisionCount, fordPolynomialWeylSum_eq_characterSum,
    fordCharacterSum, UnitAddTorus.mFourier_zero] using h

def fordPolynomialDiagonalToShifted
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p)
    (u : FordCharacterCollision
        (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
        (fun _ : Fin 1 ↦ (0 : Fin k → ℤ)) ×
      FordS4InteriorTuple s Q p) :
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ShiftedMoment (k := k) q c :
        FordS4ShiftedTuple s Q p c → Fin k → ℤ) := by
  let v := fordS4InteriorTupleToShifted c u.2
  refine ⟨((u.1.1.1.1, v), (u.1.1.2.1, v)), ?_⟩
  have hpoly :
      fordS4PolynomialMoment Ψ hdk u.1.1.1.1 =
        fordS4PolynomialMoment Ψ hdk u.1.1.2.1 := by
    simpa using u.1.2
  rw [hpoly]

theorem fordPolynomialDiagonalToShifted_injective
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) :
    Function.Injective
      (fordPolynomialDiagonalToShifted (P := P) (s := s) (Q := Q) (q := q)
        Ψ hdk c) := by
  intro u v huv
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun w ↦ w.1.1.1) huv
      · exact Subsingleton.elim _ _
    · apply Prod.ext
      · exact congrArg (fun w ↦ w.1.2.1) huv
      · exact Subsingleton.elim _ _
  · exact fordS4InteriorTupleToShifted_injective c
      (congrArg (fun w ↦ w.1.1.2) huv)

theorem fordS4_diagonal_lower
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) :
    fordPolynomialCollisionCount (P := P) (p := p) Ψ hdk * (Q / p) ^ s ≤
      fordS4Count (P := P) Ψ hdk s Q q c := by
  rw [fordS4Count_eq_shiftedCount]
  unfold fordPolynomialCollisionCount fordS4ShiftedCount
  have hbox : Nat.card (FordS4InteriorTuple s Q p) = (Q / p) ^ s := by
    simp [Nat.card_eq_fintype_card]
  rw [← hbox, ← Nat.card_prod]
  letI : Finite (FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ShiftedMoment (k := k) q c :
        FordS4ShiftedTuple s Q p c → Fin k → ℤ)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Nat.card_le_card_of_injective
    (fordPolynomialDiagonalToShifted Ψ hdk c)
    (fordPolynomialDiagonalToShifted_injective Ψ hdk c)

#print axioms fordPolynomialFourier_eq_collisionCount
#print axioms fordS4_diagonal_lower

end

end GafniTao

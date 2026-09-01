import GafniTao.FordLOffDiagonalShift

/-!
# Ford Lemma 3.3: fixed signed-shift systems

The off-diagonal branch is first partitioned by a sign and a positive shift
at every polynomial coordinate.  For fixed parameters, Ford enlarges the
lower-endpoint range to all of `[1,P]`.  This file defines the resulting
literal moment system and proves that the signed shifted moment attached to
an original congruent pair is exactly its original polynomial difference.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev FordLOffDiagonalParameter (k P m : ℕ) :=
  Fin k → Bool × FordPositiveShift P m

def fordLSignedShiftMoment
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (u : Bool × FordPositiveShift P m) (z : Fin P) : Fin k → ℤ :=
  fun j =>
    let x : ℤ := (((z : ℕ) + 1 : ℕ) : ℤ)
    let y : ℤ := ((u.2.1 * m : ℕ) : ℤ)
    if u.1 then (Ψ.poly j).eval (x + y) - (Ψ.poly j).eval x
    else (Ψ.poly j).eval x - (Ψ.poly j).eval (x + y)

def fordLFixedPolynomialMoment
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (u : FordLOffDiagonalParameter k P m)
    (z : Fin k → Fin P) : Fin k → ℤ :=
  fun j => ∑ i : Fin k, fordLSignedShiftMoment Ψ m (u i) (z i) j

def fordLFixedTotalMoment
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (u : FordLOffDiagonalParameter k P m)
    (v : (Fin k → Fin P) × FordLPowerPair s Q) : Fin k → ℤ :=
  fordLFixedPolynomialMoment Ψ m u v.1 +
    fordLPowerPairMoment k Q p q s v.2

abbrev FordLFixedSolution
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (u : FordLOffDiagonalParameter k P m) :=
  FordCharacterZero (fordLFixedTotalMoment Ψ m p q s Q u)

theorem fordLSignedShiftMoment_encoded
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (zw : FordLCongruentCoordinate P p r) (hne : zw.1.1 ≠ zw.1.2) :
    fordLSignedShiftMoment Ψ (p ^ r)
        ((fordOffDiagonalShiftCoordinate zw hne).1,
          (fordOffDiagonalShiftCoordinate zw hne).2.1)
        (fordOffDiagonalShiftCoordinate zw hne).2.2 =
      fordLCoordinateMoment Ψ zw := by
  have hs := fordOffDiagonalShiftCoordinate_spec zw hne
  dsimp only at hs
  funext j
  unfold fordLSignedShiftMoment fordLCoordinateMoment
  let u := fordOffDiagonalShiftCoordinate zw hne
  change (if u.1 then _ else _) = _
  by_cases hu : u.1 = true
  · rw [if_pos hu] at hs ⊢
    have hbase : (((zw.1.2 : ℕ) + 1 : ℕ) : ℤ) =
        ((((u.2.2 : ℕ) + 1 : ℕ) : ℤ)) := by exact_mod_cast hs.1
    have hupper : (((zw.1.1 : ℕ) + 1 : ℕ) : ℤ) =
        ((((u.2.2 : ℕ) + 1 + u.2.1.1 * (p ^ r) : ℕ) : ℤ)) := by
      exact_mod_cast hs.2
    rw [hbase, hupper]
    push_cast
    simp only [u]
  · rw [if_neg hu] at hs ⊢
    have hbase : (((zw.1.1 : ℕ) + 1 : ℕ) : ℤ) =
        ((((u.2.2 : ℕ) + 1 : ℕ) : ℤ)) := by exact_mod_cast hs.1
    have hupper : (((zw.1.2 : ℕ) + 1 : ℕ) : ℤ) =
        ((((u.2.2 : ℕ) + 1 + u.2.1.1 * (p ^ r) : ℕ) : ℤ)) := by
      exact_mod_cast hs.2
    rw [hbase, hupper]
    push_cast
    simp only [u]

#print axioms fordLSignedShiftMoment_encoded

end

end GafniTao

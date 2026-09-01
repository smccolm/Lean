import GafniTao.FordLDiagonalBranch

/-!
# Ford Lemma 3.3: exact signed-shift encoding

Every non-diagonal congruent pair in `[1,P]` has a unique sign, a unique
positive quotient `h ≤ P / p^r`, and a unique lower endpoint.  This file
formalizes that arithmetic encoding, including the endpoint bound which is
responsible for Ford's factor `(P / p^r)^k`.
-/

open Finset

namespace GafniTao

noncomputable section

abbrev FordPositiveShift (P m : ℕ) :=
  {h : ℕ // h ∈ Finset.Icc 1 (P / m)}

theorem natCard_fordPositiveShift (P m : ℕ) :
    Nat.card (FordPositiveShift P m) = P / m := by
  rw [Nat.card_eq_fintype_card]
  simp [FordPositiveShift]

theorem ford_modEq_positive_shift
    {m a b P : ℕ} (hm : 0 < m) (hab : a < b)
    (hmod : Nat.ModEq m a b) (hbP : b ≤ P) :
    ∃ h : FordPositiveShift P m, b = a + h.1 * m := by
  have hdvd : m ∣ b - a := (Nat.modEq_iff_dvd' hab.le).mp hmod
  let h : ℕ := (b - a) / m
  have hmul : h * m = b - a := by
    rw [mul_comm]
    exact Nat.mul_div_cancel' hdvd
  have hhpos : 1 ≤ h := by
    have hgap : 0 < b - a := Nat.sub_pos_of_lt hab
    apply Nat.one_le_iff_ne_zero.mpr
    intro hh
    rw [hh, zero_mul] at hmul
    exact hgap.ne' hmul.symm
  have hmulP : h * m ≤ P := by
    rw [hmul]
    exact (Nat.sub_le b a).trans hbP
  have hhP : h ≤ P / m := (Nat.le_div_iff_mul_le hm).2 hmulP
  refine ⟨⟨h, by simp [hhpos, hhP]⟩, ?_⟩
  calc
    b = a + (b - a) := by omega
    _ = a + h * m := by rw [hmul]

abbrev FordOffDiagonalShiftCoordinate (P m : ℕ) :=
  Bool × FordPositiveShift P m × Fin P

def fordOffDiagonalShiftCoordinate
    {P p r : ℕ} [NeZero (p ^ r)] (zw : FordLCongruentCoordinate P p r)
    (hne : zw.1.1 ≠ zw.1.2) : FordOffDiagonalShiftCoordinate P (p ^ r) :=
  let a : ℕ := (zw.1.1 : ℕ) + 1
  let b : ℕ := (zw.1.2 : ℕ) + 1
  if hab : a < b then
    let h := Classical.choose (ford_modEq_positive_shift (P := P)
      (NeZero.pos (p ^ r)) hab zw.2 (by simp [b]))
    (false, h, zw.1.1)
  else
    have habne : a ≠ b := by
      intro h
      apply hne
      exact Fin.ext (Nat.add_right_cancel h)
    have hba : b < a := lt_of_le_of_ne (Nat.le_of_not_gt hab) habne.symm
    let h := Classical.choose (ford_modEq_positive_shift (P := P)
      (NeZero.pos (p ^ r)) hba zw.2.symm (by simp [a]))
    (true, h, zw.1.2)

theorem fordOffDiagonalShiftCoordinate_spec
    {P p r : ℕ} [NeZero (p ^ r)] (zw : FordLCongruentCoordinate P p r)
    (hne : zw.1.1 ≠ zw.1.2) :
    let u := fordOffDiagonalShiftCoordinate zw hne
    if u.1 then
      (zw.1.2 : ℕ) + 1 = (u.2.2 : ℕ) + 1 ∧
        (zw.1.1 : ℕ) + 1 = (u.2.2 : ℕ) + 1 + u.2.1.1 * (p ^ r)
    else
      (zw.1.1 : ℕ) + 1 = (u.2.2 : ℕ) + 1 ∧
        (zw.1.2 : ℕ) + 1 = (u.2.2 : ℕ) + 1 + u.2.1.1 * (p ^ r) := by
  have habne : (zw.1.1 : ℕ) + 1 ≠ (zw.1.2 : ℕ) + 1 := by
    intro h
    apply hne
    exact Fin.ext (Nat.add_right_cancel h)
  dsimp only
  by_cases hab : (zw.1.1 : ℕ) + 1 < (zw.1.2 : ℕ) + 1
  · have hs := Classical.choose_spec (ford_modEq_positive_shift (P := P)
      (NeZero.pos (p ^ r)) hab zw.2 (by simp))
    have hbase : (zw.1.1 : ℕ) + 1 = (zw.1.1 : ℕ) + 1 := rfl
    simpa [fordOffDiagonalShiftCoordinate, hab] using And.intro hbase hs
  · have hba : (zw.1.2 : ℕ) + 1 < (zw.1.1 : ℕ) + 1 :=
      lt_of_le_of_ne (Nat.le_of_not_gt hab) habne.symm
    have hs := Classical.choose_spec (ford_modEq_positive_shift (P := P)
      (NeZero.pos (p ^ r)) hba zw.2.symm (by simp))
    have hbase : (zw.1.2 : ℕ) + 1 = (zw.1.2 : ℕ) + 1 := rfl
    simpa [fordOffDiagonalShiftCoordinate, hab] using And.intro hbase hs

theorem fordOffDiagonalShiftCoordinate_injective
    {P p r : ℕ} [NeZero (p ^ r)] :
    Function.Injective (fun z : {zw : FordLCongruentCoordinate P p r //
      zw.1.1 ≠ zw.1.2} ↦ fordOffDiagonalShiftCoordinate z.1 z.2) := by
  intro z w h
  have hz := fordOffDiagonalShiftCoordinate_spec z.1 z.2
  have hw := fordOffDiagonalShiftCoordinate_spec w.1 w.2
  dsimp only at hz hw
  let uz := fordOffDiagonalShiftCoordinate z.1 z.2
  let uw := fordOffDiagonalShiftCoordinate w.1 w.2
  have hsign : uz.1 = uw.1 := congrArg (fun u => u.1) h
  have hshift : uz.2.1.1 = uw.2.1.1 := congrArg (fun u => u.2.1.1) h
  have hbase : (uz.2.2 : ℕ) = (uw.2.2 : ℕ) := by
    exact congrArg (fun u => (u.2.2 : ℕ)) h
  dsimp only [uz, uw] at hsign hshift hbase
  by_cases hu : uz.1 = true
  · have huw : uw.1 = true := hsign.symm.trans hu
    rw [if_pos hu] at hz
    rw [if_pos huw] at hw
    have hfirst : z.1.1.1 = w.1.1.1 := Fin.ext (Nat.add_right_cancel (by
      calc
        (z.1.1.1 : ℕ) + 1 = (uz.2.2 : ℕ) + 1 + uz.2.1.1 * (p ^ r) := hz.2
        _ = (uw.2.2 : ℕ) + 1 + uw.2.1.1 * (p ^ r) := by rw [hbase, hshift]
        _ = (w.1.1.1 : ℕ) + 1 := hw.2.symm))
    have hsecond : z.1.1.2 = w.1.1.2 := Fin.ext (Nat.add_right_cancel (by
      calc
        (z.1.1.2 : ℕ) + 1 = (uz.2.2 : ℕ) + 1 := hz.1
        _ = (uw.2.2 : ℕ) + 1 := by rw [hbase]
        _ = (w.1.1.2 : ℕ) + 1 := hw.1.symm))
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hfirst hsecond
  · have huw : uw.1 ≠ true := by
      intro hwtrue
      exact hu (hsign.trans hwtrue)
    rw [if_neg hu] at hz
    rw [if_neg huw] at hw
    have hfirst : z.1.1.1 = w.1.1.1 := Fin.ext (Nat.add_right_cancel (by
      calc
        (z.1.1.1 : ℕ) + 1 = (uz.2.2 : ℕ) + 1 := hz.1
        _ = (uw.2.2 : ℕ) + 1 := by rw [hbase]
        _ = (w.1.1.1 : ℕ) + 1 := hw.1.symm))
    have hsecond : z.1.1.2 = w.1.1.2 := Fin.ext (Nat.add_right_cancel (by
      calc
        (z.1.1.2 : ℕ) + 1 = (uz.2.2 : ℕ) + 1 + uz.2.1.1 * (p ^ r) := hz.2
        _ = (uw.2.2 : ℕ) + 1 + uw.2.1.1 * (p ^ r) := by rw [hbase, hshift]
        _ = (w.1.1.2 : ℕ) + 1 := hw.2.symm))
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hfirst hsecond

#print axioms ford_modEq_positive_shift
#print axioms fordOffDiagonalShiftCoordinate_spec
#print axioms fordOffDiagonalShiftCoordinate_injective

end

end GafniTao

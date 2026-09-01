import GafniTao.FordS6Cauchy

/-!
# Ford equation (3.7): residue-diagonal collisions are `L_s` solutions

An equality of the fine maps gives both equality of the integral moments and
coordinatewise equality modulo `p^r`.  Reordering the two half-configurations
therefore produces exactly a solution of Ford equation (3.2).  The map is
injective, so no multiplicity is lost in the comparison with `L_s`.
-/

namespace GafniTao

noncomputable section

def fordS6FineCollisionToL
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) :
    FordCollisionPairs
        (fordS6FineRangeMap (s := s) (P := P) (Q := Q)
          (p := p) (q := q) (r := r) (hdk := hdk) Φ) →
      {v : FordLVariables k s P Q // FordLEquation Φ p q r v} :=
  fun z => by
    let x := z.1.1
    let y := z.1.2
    let v : FordLVariables k s P Q := ((x.1.1, y.1.1), (x.1.2, y.1.2))
    refine ⟨v, ?_, ?_⟩
    · intro i
      have hres : fordS6HalfResidue x = fordS6HalfResidue y :=
        congrArg (fun a => a.2) z.2
      have hsplit :
          fordSplitResidue (p := p) (r := r) hdk x.1.1 =
            fordSplitResidue (p := p) (r := r) hdk y.1.1 := by
        apply Prod.ext
        · exact congrArg Sigma.fst hres
        · exact congrArg (fun a => a.2.1) hres
      have hfull :
          (fun i => (fordBoxValue x.1.1 i : ZMod (p ^ r))) =
            fun i => (fordBoxValue y.1.1 i : ZMod (p ^ r)) := by
        calc
          (fun i => (fordBoxValue x.1.1 i : ZMod (p ^ r))) =
              fordJoinSplitResidue hdk
                (fordSplitResidue (p := p) (r := r) hdk x.1.1) :=
            (fordJoinSplitResidue_split hdk x.1.1).symm
          _ = fordJoinSplitResidue hdk
                (fordSplitResidue (p := p) (r := r) hdk y.1.1) :=
            congrArg (fordJoinSplitResidue hdk) hsplit
          _ = (fun i => (fordBoxValue y.1.1 i : ZMod (p ^ r))) :=
            fordJoinSplitResidue_split hdk y.1.1
      exact (ZMod.natCast_eq_natCast_iff
        (fordBoxValue x.1.1 i) (fordBoxValue y.1.1 i) (p ^ r)).mp
        (congrFun hfull i)
    · intro j
      have hmRange := congrArg (fun a => a.1) z.2
      have hm : fordS6Moment (p := p) (q := q) Φ x.1 =
          fordS6Moment (p := p) (q := q) Φ y.1 :=
        congrArg Subtype.val hmRange
      have hj := congrFun hm j
      unfold fordS6Moment fordPolynomialSumInt fordPowerSumInt at hj
      unfold fordPolynomialDifference fordPowerDifference
      dsimp [v, x, y] at hj ⊢
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      linear_combination hj

theorem fordS6FineCollisionToL_injective
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) :
    Function.Injective
      (fordS6FineCollisionToL
        (s := s) (P := P) (Q := Q) (p := p) (q := q) (r := r) Φ hdk) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg
      (fun w : {v : FordLVariables k s P Q // FordLEquation Φ p q r v} =>
        (w.1.1.1, w.1.2.1)) hab
  · apply Subtype.ext
    exact congrArg
      (fun w : {v : FordLVariables k s P Q // FordLEquation Φ p q r v} =>
        (w.1.1.2, w.1.2.2)) hab

theorem fordS6FineCollision_card_le_L
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) :
    Nat.card (FordCollisionPairs
        (fordS6FineRangeMap (s := s) (P := P) (Q := Q)
          (p := p) (q := q) (r := r) (hdk := hdk) Φ)) ≤
      fordLCount Φ s P Q p q r := by
  letI : Finite (FordS6Half k d s P Q p r hdk) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (FordCollisionPairs
      (fordS6FineRangeMap (s := s) (P := P) (Q := Q)
        (p := p) (q := q) (r := r) (hdk := hdk) Φ)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card (FordCollisionPairs
        (fordS6FineRangeMap (s := s) (P := P) (Q := Q)
          (p := p) (q := q) (r := r) (hdk := hdk) Φ)) ≤
        Nat.card {v : FordLVariables k s P Q // FordLEquation Φ p q r v} :=
      Nat.card_le_card_of_injective
        (fordS6FineCollisionToL
          (s := s) (P := P) (Q := Q) (p := p) (q := q) (r := r) Φ hdk)
        (fordS6FineCollisionToL_injective
          (s := s) (P := P) (Q := Q) (p := p) (q := q) (r := r) Φ hdk)
    _ = fordLCount Φ s P Q p q r := by
      rw [Nat.card_eq_fintype_card]
      rfl

#print axioms fordS6FineCollisionToL
#print axioms fordS6FineCollisionToL_injective
#print axioms fordS6FineCollision_card_le_L

end

end GafniTao

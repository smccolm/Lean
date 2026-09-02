import GafniTao.FordEquation54Window
import GafniTao.FordKDiagonal

/-!
# Ford Lemma 5.1: the complete degree window

For the literal source interval `B = [1,Q]` and the complete degree window
`1 <= j <= k`, Ford's incomplete mean value is exactly the complete
Vinogradov mean value `J_{s,k}(Q)`.  The proof below uses an explicit
equivalence, so the endpoint convention and the `x \mapsto x-1` reindexing
are visible in the kernel-checked statement.
-/

open Finset

namespace GafniTao

noncomputable section

/-- The literal integer interval `[1,Q]`, reindexed as `Fin Q`. -/
def fordIccOneEquivFin (Q : ℕ) :
    {b : ℕ // b ∈ Finset.Icc 1 Q} ≃ Fin Q where
  toFun b := ⟨(b : ℕ) - 1, by
    have hbpos := (Finset.mem_Icc.mp b.property).1
    have hb := (Finset.mem_Icc.mp b.property).2
    omega⟩
  invFun b := ⟨(b : ℕ) + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  left_inv b := by
    apply Subtype.ext
    change ((b : ℕ) - 1) + 1 = (b : ℕ)
    have hb := (Finset.mem_Icc.mp b.property).1
    exact Nat.sub_add_cancel hb
  right_inv b := by
    apply Fin.ext
    simp

/-- Coordinatewise reindexing of source tuples on `[1,Q]`. -/
def fordFullWindowTupleEquiv (s Q : ℕ) :
    FordLemma51BTuple s (Finset.Icc 1 Q) ≃ FordVinogradovTuple s Q where
  toFun x i := fordIccOneEquivFin Q (x i)
  invFun x i := (fordIccOneEquivFin Q).symm (x i)
  left_inv x := by
    funext i
    exact (fordIccOneEquivFin Q).left_inv (x i)
  right_inv x := by
    funext i
    exact (fordIccOneEquivFin Q).right_inv (x i)

theorem fordFullWindowTupleEquiv_value
    {s Q : ℕ} (x : FordLemma51BTuple s (Finset.Icc 1 Q)) (i : Fin s) :
    (((fordFullWindowTupleEquiv s Q x i : ℕ) + 1)) = (x i : ℕ) := by
  change ((x i : ℕ) - 1) + 1 = (x i : ℕ)
  exact Nat.sub_add_cancel (Finset.mem_Icc.mp (x i).property).1

/-- The source complete-window vector is the Vinogradov vector after the
literal endpoint-preserving reindexing. -/
theorem fordFullWindow_sourcePower_eq_vinogradov
    (k s Q : ℕ) (x : FordLemma51BTuple s (Finset.Icc 1 Q)) :
    fordLemma51WindowPowerVector k 1 k s (Finset.Icc 1 Q) x =
      fun j : FordLemma51DegreeWindow k 1 k =>
        fordVinogradovPowerVector s k Q (fordFullWindowTupleEquiv s Q x) j.1 := by
  funext j
  unfold fordLemma51WindowPowerVector fordLemma51SourcePowerVector
    fordVinogradovPowerVector
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  exact_mod_cast (fordFullWindowTupleEquiv_value x i).symm

/-- Ordered pairs counted by Ford's literal complete-window mean value. -/
abbrev FordFullWindowSolution (k s Q : ℕ) :=
  {xy : FordLemma51BTuple s (Finset.Icc 1 Q) ×
      FordLemma51BTuple s (Finset.Icc 1 Q) //
    fordLemma51WindowPowerVector k 1 k s (Finset.Icc 1 Q) xy.1 =
      fordLemma51WindowPowerVector k 1 k s (Finset.Icc 1 Q) xy.2}

theorem card_fordFullWindowSolution (k s Q : ℕ) :
    Nat.card (FordFullWindowSolution k s Q) =
      fordLemma51WindowMoment k 1 k s (Finset.Icc 1 Q) := by
  classical
  rw [Nat.card_eq_fintype_card]
  unfold FordFullWindowSolution fordLemma51WindowMoment
    fordRepresentationCount
  rw [Fintype.card_subtype]
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and, sub_eq_zero]

/-- Exact equivalence between the complete-window solutions and the complete
Vinogradov system. -/
def fordFullWindowSolutionEquiv (k s Q : ℕ) :
    FordFullWindowSolution k s Q ≃ FordPowerSolution s k Q where
  toFun v := ⟨
    (fordFullWindowTupleEquiv s Q v.1.1,
      fordFullWindowTupleEquiv s Q v.1.2), by
      funext j
      have hv := congrFun v.2 ⟨j, by omega, by omega⟩
      simpa only [fordFullWindow_sourcePower_eq_vinogradov] using hv⟩
  invFun v := ⟨
    ((fordFullWindowTupleEquiv s Q).symm v.1.1,
      (fordFullWindowTupleEquiv s Q).symm v.1.2), by
      funext j
      rw [fordFullWindow_sourcePower_eq_vinogradov,
        fordFullWindow_sourcePower_eq_vinogradov]
      simpa using congrFun v.2 j.1⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp

/-- For the full source degree window and literal interval `[1,Q]`, the
incomplete mean value in Ford Lemma 5.1 is exactly `J_{s,k}(Q)`. -/
theorem fordLemma51WindowMoment_full_eq_vinogradov
    (k s Q : ℕ) :
    fordLemma51WindowMoment k 1 k s (Finset.Icc 1 Q) =
      fordVinogradovMomentNat s k Q := by
  rw [← card_fordFullWindowSolution k s Q]
  rw [Nat.card_congr (fordFullWindowSolutionEquiv k s Q)]
  exact card_fordPowerSolution s k Q

#print axioms fordIccOneEquivFin
#print axioms fordFullWindow_sourcePower_eq_vinogradov
#print axioms fordFullWindowSolutionEquiv
#print axioms fordLemma51WindowMoment_full_eq_vinogradov

end

end GafniTao

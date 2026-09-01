import GafniTao.FordKFourier

/-!
# Ford Lemma 3.2: the diagonal lower bound for `K`

The source contradiction uses the solutions with `z_i=w_i`.  Their remaining
equations are exactly the complete Vinogradov system in the `x,y` variables.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev FordPowerSolution (s k Q : ℕ) :=
  {xy : FordBox s Q × FordBox s Q //
    fordVinogradovPowerVector s k Q xy.1 =
      fordVinogradovPowerVector s k Q xy.2}

theorem card_fordPowerSolution (s k Q : ℕ) :
    Nat.card (FordPowerSolution s k Q) =
      fordVinogradovMomentNat s k Q := by
  classical
  rw [Nat.card_eq_fintype_card]
  unfold FordPowerSolution fordVinogradovMomentNat
    fordVinogradovShiftedCountNat fordRepresentationCount
  rw [Fintype.card_subtype]
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and, sub_eq_zero]

def fordKDiagonalMap
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    FordBox k P × FordPowerSolution s k Q → FordKSolution Ψ s P Q q :=
  fun u ↦ ⟨((u.1, u.1), (u.2.1.1, u.2.1.2)), by
    intro j
    have hpower := congrFun u.2.2 j
    unfold fordVinogradovPowerVector at hpower
    unfold fordPolynomialDifference fordPowerDifference
    simp only [sub_self, Finset.sum_const_zero, zero_add,
      Finset.sum_sub_distrib, fordBoxValue]
    push_cast
    rw [hpower, sub_self, mul_zero]⟩

theorem fordKDiagonalMap_injective
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    Function.Injective (fordKDiagonalMap Ψ :
      FordBox k P × FordPowerSolution s k Q → FordKSolution Ψ s P Q q) := by
  intro u v huv
  have hz := congrArg (fun w ↦ w.1.1.1) huv
  have hxy := congrArg (fun w ↦ (w.1.2.1, w.1.2.2)) huv
  change u.1 = v.1 at hz
  change u.2.1 = v.2.1 at hxy
  exact Prod.ext hz (Subtype.ext hxy)

theorem fordK_diagonal_lower
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) :
    P ^ k * fordVinogradovMomentNat s k Q ≤ fordKCount Ψ s P Q q := by
  have hinj := fordKDiagonalMap_injective (s := s) (P := P) (Q := Q) (q := q) Ψ
  have hcard : Nat.card (FordBox k P × FordPowerSolution s k Q) ≤
      Nat.card (FordKSolution Ψ s P Q q) :=
    Nat.card_le_card_of_injective _ hinj
  calc
    P ^ k * fordVinogradovMomentNat s k Q =
        Nat.card (FordBox k P × FordPowerSolution s k Q) := by
      rw [Nat.card_prod, card_fordPowerSolution]
      simp [Nat.card_eq_fintype_card]
    _ ≤ Nat.card (FordKSolution Ψ s P Q q) := hcard
    _ = fordKCount Ψ s P Q q := by
      rw [Nat.card_eq_fintype_card]
      rfl

#print axioms fordK_diagonal_lower

end

end GafniTao

import GafniTao.FordLemma34EventualData

/-! # Ford Lemma 3.4: the initial power system -/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Join the `x` variables before the `z` variables. -/
def fordInitialJoin {k s P : ℕ} (v : FordKVariables k s P P) :
    FordBox (s + k) P × FordBox (s + k) P :=
  (Fin.append v.2.1 v.1.1, Fin.append v.2.2 v.1.2)

/-- Split a Vinogradov tuple into its first `s` and final `k` coordinates. -/
def fordInitialSplit {k s P : ℕ}
    (v : FordBox (s + k) P × FordBox (s + k) P) :
    FordKVariables k s P P :=
  ((fun i => v.1 (Fin.natAdd s i), fun i => v.2 (Fin.natAdd s i)),
    (fun i => v.1 (Fin.castAdd k i), fun i => v.2 (Fin.castAdd k i)))

theorem fordInitialSplit_join {k s P : ℕ} (v : FordKVariables k s P P) :
    fordInitialSplit (fordInitialJoin v) = v := by
  rcases v with ⟨⟨z, w⟩, ⟨x, y⟩⟩
  ext i <;> simp [fordInitialSplit, fordInitialJoin]

theorem fordInitialJoin_split {k s P : ℕ}
    (v : FordBox (s + k) P × FordBox (s + k) P) :
    fordInitialJoin (fordInitialSplit v) = v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · apply _root_.funext
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
      simp [fordInitialSplit, fordInitialJoin]
  · apply _root_.funext
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
      simp [fordInitialSplit, fordInitialJoin]

/-- The underlying variable boxes are canonically equivalent. -/
def fordInitialVariablesEquiv (k s P : ℕ) :
    FordKVariables k s P P ≃
      (FordBox (s + k) P × FordBox (s + k) P) where
  toFun := fordInitialJoin
  invFun := fordInitialSplit
  left_inv := fordInitialSplit_join
  right_inv := fordInitialJoin_split

/-- For the initial system and `q=1`, Ford's K-equation is exactly the
Vinogradov power-vector equality on the joined `s+k` variables. -/
theorem fordInitialKEquation_iff
    {k s P : ℕ} (v : FordKVariables k s P P) :
    FordKEquation (fordInitialIntegerPowerSystem k) 1 v ↔
      fordVinogradovPowerVector (s + k) k P (fordInitialJoin v).1 =
        fordVinogradovPowerVector (s + k) k P (fordInitialJoin v).2 := by
  constructor
  · intro h
    funext J
    let A : ℤ := ∑ i : Fin k,
      (((v.1.1 i : ℕ) + 1 : ℤ) ^ ((J : ℕ) + 1))
    let B : ℤ := ∑ i : Fin k,
      (((v.1.2 i : ℕ) + 1 : ℤ) ^ ((J : ℕ) + 1))
    let C : ℤ := ∑ i : Fin s,
      (((v.2.1 i : ℕ) + 1 : ℤ) ^ ((J : ℕ) + 1))
    let D : ℤ := ∑ i : Fin s,
      (((v.2.2 i : ℕ) + 1 : ℤ) ^ ((J : ℕ) + 1))
    have hJ : A - B + (C - D) = 0 := by
      have hraw := h J
      simp only [fordPolynomialDifference,
        fordInitialIntegerPowerSystem, Polynomial.eval_pow, Polynomial.eval_X,
        fordPowerDifference, fordBoxValue, Nat.cast_add, Nat.cast_one,
        one_pow, one_mul] at hraw
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hraw
      exact hraw
    simp only [fordVinogradovPowerVector, fordInitialJoin, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right]
    change C + A = D + B
    linarith
  · intro h J
    let A : ℤ := ∑ i : Fin k,
      (((v.1.1 i : ℕ) + 1 : ℤ) ^ ((J : ℕ) + 1))
    let B : ℤ := ∑ i : Fin k,
      (((v.1.2 i : ℕ) + 1 : ℤ) ^ ((J : ℕ) + 1))
    let C : ℤ := ∑ i : Fin s,
      (((v.2.1 i : ℕ) + 1 : ℤ) ^ ((J : ℕ) + 1))
    let D : ℤ := ∑ i : Fin s,
      (((v.2.2 i : ℕ) + 1 : ℤ) ^ ((J : ℕ) + 1))
    have hJ := congrFun h J
    simp only [fordVinogradovPowerVector, fordInitialJoin, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right] at hJ
    change C + A = D + B at hJ
    have habcd : A - B + (C - D) = 0 := by linarith
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib] at habcd
    simpa only [fordPolynomialDifference,
      fordInitialIntegerPowerSystem, Polynomial.eval_pow, Polynomial.eval_X,
      fordPowerDifference, fordBoxValue, Nat.cast_add, Nat.cast_one,
      one_pow, one_mul] using habcd

/-- Exact equivalence between initial K-solutions and the complete
Vinogradov solutions of length `s+k`. -/
def fordInitialSolutionEquiv (k s P : ℕ) :
    {v : FordKVariables k s P P //
      FordKEquation (fordInitialIntegerPowerSystem k) 1 v} ≃
      FordPowerSolution (s + k) k P where
  toFun v := ⟨fordInitialJoin v.1, (fordInitialKEquation_iff v.1).mp v.2⟩
  invFun v := ⟨fordInitialSplit v.1, by
    apply (fordInitialKEquation_iff (fordInitialSplit v.1)).mpr
    rw [fordInitialJoin_split]
    exact v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact fordInitialSplit_join v.1
  right_inv v := by
    apply Subtype.ext
    exact fordInitialJoin_split v.1

/-- The exact identity used in the final application of Lemma 3.2. -/
theorem fordKCount_initial_eq_vinogradov
    (k s P : ℕ) :
    fordKCount (fordInitialIntegerPowerSystem k) s P P 1 =
      fordVinogradovMomentNat (s + k) k P := by
  unfold fordKCount
  rw [Fintype.card_congr (fordInitialSolutionEquiv k s P)]
  simpa [Nat.card_eq_fintype_card] using card_fordPowerSolution (s + k) k P

/-- Real-endpoint version of the same source identity. -/
theorem fordKCountReal_initial_eq_vinogradov
    (k s : ℕ) (P : ℝ) :
    fordKCountReal (fordInitialIntegerPowerSystem k) s P P 1 =
      fordVinogradovMoment (s + k) k P := by
  unfold fordKCountReal fordVinogradovMoment
  exact fordKCount_initial_eq_vinogradov k s ⌊P⌋₊

#print axioms fordInitialKEquation_iff
#print axioms fordInitialSolutionEquiv
#print axioms fordKCount_initial_eq_vinogradov
#print axioms fordKCountReal_initial_eq_vinogradov

end

end GafniTao

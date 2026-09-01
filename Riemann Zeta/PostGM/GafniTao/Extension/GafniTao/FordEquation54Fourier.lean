import GafniTao.FordEquation54Expansion

/-!
# Ford Lemma 5.1: the product Fourier identity in equation (5.4)

This file takes the one-dimensional sinc-square Fourier series proved in
`FordTentSeries` and forms its literal `k`-fold product.  Absolute convergence
is part of the theorem, so the lattice rearrangement used in Ford's equation
(5.4) is kernel checked rather than treated formally.
-/

open Finset
open scoped BigOperators NNReal

namespace GafniTao

noncomputable section

/-- An absolutely summable finite family of complex series may be multiplied
coordinate by coordinate over the full integer lattice. -/
theorem hasSum_fin_pi_prod_complex
    (k : ℕ) (f : (j : Fin k) → ℤ → ℂ) (a : Fin k → ℂ)
    (hf : ∀ j, HasSum (f j) (a j))
    (habs : ∀ j, Summable (fun n => ‖f j n‖)) :
    HasSum (fun c : Fin k → ℤ => ∏ j : Fin k, f j (c j))
      (∏ j : Fin k, a j) := by
  induction k with
  | zero =>
      convert (hasSum_fintype
        (fun c : Fin 0 → ℤ => ∏ j : Fin 0, f j (c j))) using 1
      all_goals simp
  | succ k ih =>
      let f0 : (j : Fin k) → ℤ → ℂ := fun j => f j.castSucc
      let a0 : Fin k → ℂ := fun j => a j.castSucc
      have h0 : HasSum (fun c : Fin k → ℤ => ∏ j : Fin k, f0 j (c j))
          (∏ j : Fin k, a0 j) :=
        ih f0 a0 (fun j => hf j.castSucc) (fun j => habs j.castSucc)
      have h0abs : Summable (fun c : Fin k → ℤ =>
          ‖∏ j : Fin k, f0 j (c j)‖) := h0.summable.norm
      have hlast := hf (Fin.last k)
      have hlastAbs := habs (Fin.last k)
      have hcross := summable_mul_of_summable_norm h0abs hlastAbs
      have hpair := h0.mul hlast hcross
      apply ((Fin.succFunEquiv ℤ k).symm.hasSum_iff).mp
      convert hpair using 1
      · funext p
        simp only [Function.comp_apply]
        rw [Fin.prod_univ_castSucc]
        congr 1
        · apply Finset.prod_congr rfl
          intro j _hj
          change f j.castSucc
              (Fin.append p.1 (fun _ : Fin 1 => p.2) (Fin.castAdd 1 j)) =
            f j.castSucc (p.1 j)
          rw [Fin.append_left]
        · have hlastEq : Fin.last k = Fin.natAdd k (0 : Fin 1) := by
            ext
            simp
          rw [hlastEq]
          change f (Fin.natAdd k 0)
              (Fin.append p.1 (fun _ : Fin 1 => p.2) (Fin.natAdd k 0)) =
            f (Fin.natAdd k 0) p.2
          rw [Fin.append_right]
      · rw [Fin.prod_univ_castSucc]

/-- The `j`-th summand in Ford's product Fourier series. -/
def fordLemma51CoordinateFourierTerm
    (k r M : ℕ) (j : Fin k) (y : Fin k → ℝ) (n : ℤ) : ℂ :=
  (fordSincSquareWeight r M ((j : ℕ) + 1) (n : ℝ) : ℂ) *
    fordAdditiveCharacter ((n : ℝ) * y j)

/-- The real, nonnegative tent factor of the `j`-th coordinate series. -/
def fordLemma51CoordinateTentFactor
    (k r M : ℕ) (j : Fin k) (y : Fin k → ℝ) : ℝ :=
  ((Real.pi ^ 2 * ((r * M ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2) *
      fordTent (y j)
        (1 / (2 * ((r * M ^ ((j : ℕ) + 1) : ℕ) : ℝ))))

/-- The exact complex value of the `j`-th coordinate series. -/
def fordLemma51CoordinateTentValue
    (k r M : ℕ) (j : Fin k) (y : Fin k → ℝ) : ℂ :=
  (fordLemma51CoordinateTentFactor k r M j y : ℂ)

theorem hasSum_fordLemma51CoordinateFourierTerm
    {k r M : ℕ} (hr : 0 < r) (hM : 0 < M)
    (j : Fin k) (y : Fin k → ℝ) :
    HasSum (fordLemma51CoordinateFourierTerm k r M j y)
      (fordLemma51CoordinateTentValue k r M j y) := by
  exact hasSum_fordSincSquareWeight_character hr hM (y j)

theorem summable_norm_fordLemma51CoordinateFourierTerm
    {k r M : ℕ} (hr : 0 < r) (hM : 0 < M)
    (j : Fin k) (y : Fin k → ℝ) :
    Summable (fun n : ℤ =>
      ‖fordLemma51CoordinateFourierTerm k r M j y n‖) := by
  have hw := summable_fordLemma51CoordinateWeight
    (j := (j : ℕ) + 1) hr hM
  have hwR : Summable (fun n : ℤ =>
      (fordSincSquareWeight r M ((j : ℕ) + 1) (n : ℝ) : ℝ)) :=
    NNReal.summable_coe.mpr hw
  convert hwR using 1
  funext n
  unfold fordLemma51CoordinateFourierTerm fordAdditiveCharacter
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fordSincSquareWeight_nonneg r M ((j : ℕ) + 1) (n : ℝ)),
    Complex.norm_exp]
  simp

/-- The exact `k`-coordinate Fourier/tent product.  This is the analytic
factorization at the heart of Ford's displayed equation (5.4). -/
theorem hasSum_fordLemma51CoordinateFourierProduct
    {k r M : ℕ} (hr : 0 < r) (hM : 0 < M) (y : Fin k → ℝ) :
    HasSum
      (fun c : Fin k → ℤ =>
        ∏ j : Fin k, fordLemma51CoordinateFourierTerm k r M j y (c j))
      (∏ j : Fin k, fordLemma51CoordinateTentValue k r M j y) := by
  exact hasSum_fin_pi_prod_complex k
    (fun j => fordLemma51CoordinateFourierTerm k r M j y)
    (fun j => fordLemma51CoordinateTentValue k r M j y)
    (fun j => hasSum_fordLemma51CoordinateFourierTerm hr hM j y)
    (fun j => summable_norm_fordLemma51CoordinateFourierTerm hr hM j y)

theorem fordLemma51CoordinateFourierProduct_eq
    {k r M : ℕ} (y : Fin k → ℝ) (c : Fin k → ℤ) :
    (∏ j : Fin k, fordLemma51CoordinateFourierTerm k r M j y (c j)) =
      (fordLemma51WeightProduct k r M c : ℂ) *
        fordAdditiveCharacter (∑ j : Fin k, (c j : ℝ) * y j) := by
  unfold fordLemma51CoordinateFourierTerm fordLemma51WeightProduct
    fordLemma51CoordinateWeight
  rw [Finset.prod_mul_distrib]
  congr 1
  · push_cast
    apply Finset.prod_congr rfl
    intro j _hj
    rfl
  · rw [← fordAdditiveCharacter_sum Finset.univ]

/-- The product Fourier identity, expressed directly with Ford's lattice
weight rather than as a product of coordinate functions. -/
theorem hasSum_fordLemma51WeightProduct_character
    {k r M : ℕ} (hr : 0 < r) (hM : 0 < M) (y : Fin k → ℝ) :
    HasSum
      (fun c : Fin k → ℤ =>
        (fordLemma51WeightProduct k r M c : ℂ) *
          fordAdditiveCharacter (∑ j : Fin k, (c j : ℝ) * y j))
      (∏ j : Fin k, fordLemma51CoordinateTentValue k r M j y) := by
  exact HasSum.congr_fun
    (hasSum_fordLemma51CoordinateFourierProduct hr hM y)
    (fun c => (fordLemma51CoordinateFourierProduct_eq (r := r) (M := M) y c).symm)

/-- The coordinate vector that appears after a tuple pair has been grouped
by its signed power-difference vector. -/
def fordLemma51DifferenceCoordinate
    (k : ℕ) (t z : ℝ) (d : Fin k → ℤ) : Fin k → ℝ :=
  fun j => fordTaylorGamma t z (j : ℕ) * (d j : ℝ)

theorem fordLemma51DifferencePhase_eq_coordinateSum
    (k : ℕ) (t z : ℝ) (d c : Fin k → ℤ) :
    fordLemma51DifferencePhase k t z d c =
      ∑ j : Fin k, (c j : ℝ) * fordLemma51DifferenceCoordinate k t z d j := by
  unfold fordLemma51DifferencePhase fordLemma51DifferenceCoordinate
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exact lattice Fourier evaluation for one fixed Ford displacement vector. -/
theorem hasSum_fordLemma51DifferenceLattice
    {k r M : ℕ} (hr : 0 < r) (hM : 0 < M)
    (t z : ℝ) (d : Fin k → ℤ) :
    HasSum
      (fun c : Fin k → ℤ =>
        (fordLemma51WeightProduct k r M c : ℂ) *
          fordAdditiveCharacter (fordLemma51DifferencePhase k t z d c))
      (∏ j : Fin k, fordLemma51CoordinateTentValue k r M j
        (fordLemma51DifferenceCoordinate k t z d)) := by
  have h := hasSum_fordLemma51WeightProduct_character hr hM
    (fordLemma51DifferenceCoordinate k t z d)
  apply HasSum.congr_fun h
  intro c
  rw [fordLemma51DifferencePhase_eq_coordinateSum]

#print axioms hasSum_fin_pi_prod_complex
#print axioms hasSum_fordLemma51CoordinateFourierTerm
#print axioms summable_norm_fordLemma51CoordinateFourierTerm
#print axioms hasSum_fordLemma51CoordinateFourierProduct
#print axioms fordLemma51CoordinateFourierProduct_eq
#print axioms hasSum_fordLemma51WeightProduct_character
#print axioms fordLemma51DifferencePhase_eq_coordinateSum
#print axioms hasSum_fordLemma51DifferenceLattice

end

end GafniTao

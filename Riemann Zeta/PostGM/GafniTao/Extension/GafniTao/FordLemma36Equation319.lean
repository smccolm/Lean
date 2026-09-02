import GafniTao.FordLemma36ReciprocalSum

/-! # Ford Lemma 3.6: equation (3.19) -/

namespace GafniTao

noncomputable section

theorem fordPotential36_exp
    {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2) :
    Real.exp (fordPotential36 d) = d * (2 - d) * Real.exp d := by
  unfold fordPotential36
  rw [Real.exp_add, Real.exp_add, Real.exp_log hd0, Real.exp_log (sub_pos.mpr hd2)]
  ring

theorem fordPotential36_iterated_numeric
    {k n : ℕ} (hk : 1000 ≤ k) (hn : 1 ≤ n)
    (habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordPotential36 (fordDSequence36 k n) ≤
      fordPotential36 (fordDSequence36 k 0) -
        (n : ℝ) * fordPotentialLoss36 k +
          67 / (50 * (k : ℝ)) := by
  have hiter := fordPotential36_iterated hk habove
  have herr := fordReciprocalError36_bound hk hn habove
  linarith

theorem fordEquation319
    {k n : ℕ} (hk : 1000 ≤ k) (hn : 1 ≤ n)
    (habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordDSequence36 k n ≤
      (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) /
        ((2 - fordDSequence36 k n) * Real.exp (fordDSequence36 k n)) *
          Real.exp (-(n : ℝ) * fordPotentialLoss36 k +
            67 / (50 * (k : ℝ))) := by
  have hbounds := fordDSequence36_bounds_of_above hk habove
  have hd0 := hbounds.1
  have hdUpper := hbounds.2
  have hinit0 : 0 < fordDSequence36 k 0 := by
    exact (fordDSequence36_bounds_of_above hk
      (n := 0) (fun _ h => by omega)).1
  have hinitHalf : fordDSequence36 k 0 < 1 / 2 := by
    rw [fordDSequence36_zero]
    have hk0 : (0 : ℝ) < k := by positivity
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k)]
    nlinarith
  have hdHalf : fordDSequence36 k n < 1 / 2 :=
    lt_of_le_of_lt hdUpper hinitHalf
  have hpot := fordPotential36_iterated_numeric hk hn habove
  have hexp := Real.exp_le_exp.mpr hpot
  rw [fordPotential36_exp hd0 (by linarith),
    show fordPotential36 (fordDSequence36 k 0) -
        (n : ℝ) * fordPotentialLoss36 k + 67 / (50 * (k : ℝ)) =
      fordPotential36 (fordDSequence36 k 0) +
        (-(n : ℝ) * fordPotentialLoss36 k + 67 / (50 * (k : ℝ))) by ring,
    Real.exp_add, fordPotential36_exp hinit0 (by linarith)] at hexp
  have hden : 0 < (2 - fordDSequence36 k n) *
      Real.exp (fordDSequence36 k n) := by
    exact mul_pos (by linarith) (Real.exp_pos _)
  rw [show
    (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) /
        ((2 - fordDSequence36 k n) * Real.exp (fordDSequence36 k n)) *
          Real.exp (-(n : ℝ) * fordPotentialLoss36 k +
            67 / (50 * (k : ℝ))) =
      ((fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) *
          Real.exp (-(n : ℝ) * fordPotentialLoss36 k +
            67 / (50 * (k : ℝ)))) /
        ((2 - fordDSequence36 k n) * Real.exp (fordDSequence36 k n)) by ring]
  rw [le_div_iff₀ hden]
  calc
    fordDSequence36 k n *
        ((2 - fordDSequence36 k n) * Real.exp (fordDSequence36 k n)) =
      fordDSequence36 k n * (2 - fordDSequence36 k n) *
        Real.exp (fordDSequence36 k n) := by ring
    _ ≤ fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
        Real.exp (fordDSequence36 k 0) *
          Real.exp (-(n : ℝ) * fordPotentialLoss36 k +
            67 / (50 * (k : ℝ))) := hexp
    _ = (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) *
        Real.exp (-(n : ℝ) * fordPotentialLoss36 k +
          67 / (50 * (k : ℝ))) := by ring

#print axioms fordPotential36_exp
#print axioms fordPotential36_iterated_numeric
#print axioms fordEquation319

end

end GafniTao

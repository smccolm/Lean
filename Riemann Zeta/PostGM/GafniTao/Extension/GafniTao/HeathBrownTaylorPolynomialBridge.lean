import GafniTao.HeathBrownTaylorRemainder

/-!
# The source Taylor polynomial and Mathlib's Taylor polynomial

Heath-Brown differentiates the degree-`k-1` Taylor phase.  The resulting
degree-`k-2` polynomial is exactly Mathlib's Taylor polynomial for `f'`.
This file proves that normalization bridge, including the index shift and
factorials.
-/

open Set Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The derivative polynomial occurring in the source definition of `g_n'`. -/
noncomputable def heathBrownTaylorDerivativePolynomial
    (k : ℕ) (f : ℝ → ℝ) (n x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k - 1),
    iteratedDeriv (j + 1) f n * x ^ j / (j.factorial : ℝ)

theorem iteratedDeriv_deriv_eq_succ
    (j : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv j (deriv f) = iteratedDeriv (j + 1) f := by
  exact (iteratedDeriv_succ' (n := j) (f := f)).symm

/-- The literal finite sum in the source is Mathlib's ordinary Taylor
polynomial evaluated at the shifted point. -/
theorem taylorWithinEval_univ_eq_heathBrownTaylorPolynomial
    (k : ℕ) (f : ℝ → ℝ) (n x : ℝ) :
    taylorWithinEval f k Set.univ n (n + x) =
      heathBrownTaylorPolynomial (k + 1) f n x := by
  rw [taylor_within_apply]
  unfold heathBrownTaylorPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_univ]
  simp only [smul_eq_mul]
  ring

/-- Exact identification of the source derivative polynomial with
`taylorWithinEval (deriv f)`. -/
theorem taylorWithinEval_deriv_eq_heathBrownTaylorDerivativePolynomial
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x : ℝ}
    (hx : 0 < x)
    (hf : ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n) :
    taylorWithinEval (deriv f) (k - 2) (Set.Icc n (n + x)) n (n + x) =
      heathBrownTaylorDerivativePolynomial k f n x := by
  rw [taylor_within_apply]
  unfold heathBrownTaylorDerivativePolynomial
  have hcard : k - 2 + 1 = k - 1 := by omega
  rw [hcard]
  apply Finset.sum_congr rfl
  intro j hj
  have hn : n ∈ Set.Icc n (n + x) := ⟨le_rfl, by linarith⟩
  have hud : UniqueDiffOn ℝ (Set.Icc n (n + x)) := by
    exact uniqueDiffOn_Icc (by linarith)
  have hjlt : j < k - 1 := Finset.mem_range.mp hj
  have hjle : j ≤ k - 2 := by omega
  have hfj : ContDiffAt ℝ (j : ℕ) (deriv f) n := by
    apply hf.of_le
    exact_mod_cast hjle
  rw [iteratedDerivWithin_eq_iteratedDeriv hud hfj hn]
  rw [iteratedDeriv_deriv_eq_succ]
  simp only [smul_eq_mul]
  ring

/-- On a positive shift, the previous bridge uses the ordinary ordered
interval and no endpoint convention is hidden. -/
theorem taylorWithinEval_deriv_eq_heathBrownTaylorDerivativePolynomial_of_pos
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x : ℝ}
    (hx : 0 < x)
    (hf : ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n) :
    taylorWithinEval (deriv f) (k - 2) (Set.Icc n (n + x)) n (n + x) =
      heathBrownTaylorDerivativePolynomial k f n x :=
  taylorWithinEval_deriv_eq_heathBrownTaylorDerivativePolynomial hk hx hf

#print axioms iteratedDeriv_deriv_eq_succ
#print axioms taylorWithinEval_univ_eq_heathBrownTaylorPolynomial
#print axioms taylorWithinEval_deriv_eq_heathBrownTaylorDerivativePolynomial
#print axioms taylorWithinEval_deriv_eq_heathBrownTaylorDerivativePolynomial_of_pos

end

end GafniTao

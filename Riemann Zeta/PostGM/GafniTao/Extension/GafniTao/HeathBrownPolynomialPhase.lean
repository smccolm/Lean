import GafniTao.HeathBrownSourceAverage
import GafniTao.FordLemma51Fibers

/-!
# Polynomial phases in Heath-Brown Lemma 1

This file fixes the literal Taylor polynomial used in the source and proves
that its constant term and integral coefficient changes have no effect on the
norm of the associated exponential sum.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem heathBrownPhase_eq_fordAdditiveCharacter (x : ℝ) :
    heathBrownPhase x = fordAdditiveCharacter x := by
  unfold heathBrownPhase fordAdditiveCharacter
  congr 1
  push_cast
  ring

theorem heathBrownPhase_add (x y : ℝ) :
    heathBrownPhase (x + y) = heathBrownPhase x * heathBrownPhase y := by
  simp only [heathBrownPhase_eq_fordAdditiveCharacter,
    fordAdditiveCharacter_add]

theorem heathBrownPhase_int (z : ℤ) :
    heathBrownPhase (z : ℝ) = 1 := by
  rw [heathBrownPhase_eq_fordAdditiveCharacter]
  unfold fordAdditiveCharacter
  have h := Complex.exp_int_mul_two_pi_mul_I z
  convert h using 1
  push_cast
  ring_nf

theorem heathBrownPhase_add_int (x : ℝ) (z : ℤ) :
    heathBrownPhase (x + z) = heathBrownPhase x := by
  rw [heathBrownPhase_add, heathBrownPhase_int, mul_one]

/-- Heath-Brown's Taylor polynomial
`f_n(x)=sum_{j=0}^{k-1} f^(j)(n)x^j/j!`. -/
noncomputable def heathBrownTaylorPolynomial
    (k : ℕ) (f : ℝ → ℝ) (n x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k,
    iteratedDeriv j f n * x ^ j / (j.factorial : ℝ)

/-- The same Taylor phase after removing its constant term. -/
noncomputable def heathBrownReducedTaylorPolynomial
    (k : ℕ) (f : ℝ → ℝ) (n x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 k,
    iteratedDeriv j f n * x ^ j / (j.factorial : ℝ)

theorem heathBrownTaylorPolynomial_eq_constant_add_reduced
    {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ) (n x : ℝ) :
    heathBrownTaylorPolynomial k f n x =
      f n + heathBrownReducedTaylorPolynomial k f n x := by
  unfold heathBrownTaylorPolynomial heathBrownReducedTaylorPolynomial
  have hrange : Finset.range k = insert 0 (Finset.Ico 1 k) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp

noncomputable def heathBrownTaylorPolynomialSum
    (k Q : ℕ) (f : ℝ → ℝ) (n : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 Q,
    heathBrownPhase (heathBrownTaylorPolynomial k f n h)

noncomputable def heathBrownReducedTaylorPolynomialSum
    (k Q : ℕ) (f : ℝ → ℝ) (n : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 Q,
    heathBrownPhase (heathBrownReducedTaylorPolynomial k f n h)

theorem heathBrownTaylorPolynomialSum_eq_phase_mul_reduced
    {k : ℕ} (hk : 1 ≤ k) (Q : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    heathBrownTaylorPolynomialSum k Q f n =
      heathBrownPhase (f n) *
        heathBrownReducedTaylorPolynomialSum k Q f n := by
  unfold heathBrownTaylorPolynomialSum heathBrownReducedTaylorPolynomialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← heathBrownPhase_add,
    ← heathBrownTaylorPolynomial_eq_constant_add_reduced hk]

/-- Removing the constant Taylor coefficient preserves the exact norm. -/
theorem norm_heathBrownTaylorPolynomialSum_eq_reduced
    {k : ℕ} (hk : 1 ≤ k) (Q : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    ‖heathBrownTaylorPolynomialSum k Q f n‖ =
      ‖heathBrownReducedTaylorPolynomialSum k Q f n‖ := by
  rw [heathBrownTaylorPolynomialSum_eq_phase_mul_reduced hk, norm_mul,
    norm_heathBrownPhase, one_mul]

/-- An integer-valued polynomial perturbation is invisible to `e(x)`. -/
theorem heathBrownPhase_polynomial_add_integer
    {d : ℕ} (c : Fin d → ℝ) (z : Fin d → ℤ) (x : ℕ) :
    heathBrownPhase
        ((∑ j : Fin d, c j * (x : ℝ) ^ ((j : ℕ) + 1)) +
          ∑ j : Fin d, (z j : ℝ) * (x : ℝ) ^ ((j : ℕ) + 1)) =
      heathBrownPhase
        (∑ j : Fin d, c j * (x : ℝ) ^ ((j : ℕ) + 1)) := by
  let Z : ℤ := ∑ j : Fin d, z j * (x : ℤ) ^ ((j : ℕ) + 1)
  have hcast :
      (Z : ℝ) =
        ∑ j : Fin d, (z j : ℝ) * (x : ℝ) ^ ((j : ℕ) + 1) := by
    dsimp only [Z]
    push_cast
    rfl
  rw [← hcast, heathBrownPhase_add_int]

#print axioms heathBrownPhase_eq_fordAdditiveCharacter
#print axioms heathBrownPhase_add
#print axioms heathBrownPhase_int
#print axioms heathBrownPhase_add_int
#print axioms heathBrownTaylorPolynomial_eq_constant_add_reduced
#print axioms heathBrownTaylorPolynomialSum_eq_phase_mul_reduced
#print axioms norm_heathBrownTaylorPolynomialSum_eq_reduced
#print axioms heathBrownPhase_polynomial_add_integer

end

end GafniTao

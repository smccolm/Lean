import GafniTao.SharpPerronPhysical

/-!
# The exact sharp cutoff inside Perron's series

The cutoff below uses `n ≤ x`, exactly matching `Chebyshev.psi`.  Keeping the
endpoint in the definition prevents a hidden half-weight convention.
-/

open scoped BigOperators

namespace GafniTao

/-- The complex-valued sharp cutoff whose von Mangoldt sum is `psi(x)`. -/
noncomputable def sharpPerronCutoff (x : ℝ) (n : ℕ) : ℂ :=
  if (n : ℝ) ≤ x then 1 else 0

/-- The cutoff series is exactly the Mathlib Chebyshev function, including an
integral right endpoint. -/
theorem tsum_vonMangoldt_mul_sharpPerronCutoff_eq_psi
    {x : ℝ} (hx : 0 ≤ x) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        sharpPerronCutoff x n = (Chebyshev.psi x : ℂ) := by
  rw [tsum_eq_sum (s := Finset.Icc 0 ⌊x⌋₊)]
  · calc
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronCutoff x n =
          ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℂ) := by
              apply Finset.sum_congr rfl
              intro n hn
              have hnle : (n : ℝ) ≤ x :=
                (Nat.le_floor_iff hx).mp (Finset.mem_Icc.mp hn).2
              simp [sharpPerronCutoff, hnle]
      _ = ((∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
              exact (Complex.ofReal_sum _ _).symm
      _ = (Chebyshev.psi x : ℂ) := by
              rw [Chebyshev.psi_eq_sum_Icc]
  · intro n hn
    have hnFloor : ¬ n ≤ ⌊x⌋₊ := by
      intro hnle
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnle⟩)
    have hnx : ¬ (n : ℝ) ≤ x := by
      simpa [Nat.le_floor_iff hx] using hnFloor
    simp [sharpPerronCutoff, hnx]

/-- Absolute convergence of the exact von Mangoldt-weighted Perron-kernel
series on every line `c>1`. -/
theorem summable_vonMangoldt_mul_sharpPerronKernel
    {c T x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        sharpPerronKernel c T x n) := by
  have hSeries := hasSum_integral_sharpPerronSeriesTerm (T := T) hc hx
  have hScaled := hSeries.mul_left (1 / (2 * Real.pi) : ℂ)
  refine (HasSum.congr_fun hScaled (fun n => ?_)).summable
  exact
    (normalized_integral_sharpPerronSeriesTerm_eq
      (c := c) (T := T) (x := x) n).symm

/-- The cutoff series is finite, hence summable. -/
theorem summable_vonMangoldt_mul_sharpPerronCutoff
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        sharpPerronCutoff x n) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 0 ⌊x⌋₊)
  intro n hn
  have hnFloor : ¬ n ≤ ⌊x⌋₊ := by
    intro hnle
    exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnle⟩)
  have hnx : ¬ (n : ℝ) ≤ x := by
    simpa [Nat.le_floor_iff hx] using hnFloor
  simp [sharpPerronCutoff, hnx]

/-- Exact decomposition of the right-line Perron integral error into the
termwise finite-height cutoff error. -/
theorem sharpPerron_logDerivative_sub_psi_eq_tsum_cutoffError
    {c T x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) *
          (∫ t in (-T)..T,
            (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) /
                riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I)) *
              (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                ((c : ℂ) + (t : ℂ) * Complex.I)) -
        (Chebyshev.psi x : ℂ) =
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
            sharpPerronKernel c T x n -
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            sharpPerronCutoff x n) := by
  rw [sharpPerron_logDerivative_eq_tsum_kernels hc hx]
  rw [← tsum_vonMangoldt_mul_sharpPerronCutoff_eq_psi hx.le]
  rw [(summable_vonMangoldt_mul_sharpPerronKernel hc hx).tsum_sub
    (summable_vonMangoldt_mul_sharpPerronCutoff hx.le)]

end GafniTao

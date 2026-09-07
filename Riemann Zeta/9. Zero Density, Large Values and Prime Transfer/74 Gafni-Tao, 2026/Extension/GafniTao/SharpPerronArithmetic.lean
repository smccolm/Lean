import GafniTao.SharpPerronFarBounds

/-!
# Assembly of the arithmetic sharp-Perron error

The complete error series is split pointwise between the literal finite
half-integral harmonic kernel and the positive von Mangoldt Dirichlet series.
This is the arithmetic core of the classical `x log^2 x / T` remainder.
-/

open scoped BigOperators

namespace GafniTao

private noncomputable def sharpPerronNearWeight (x : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Finset.range (2 * ⌊x⌋₊ + 2) then
    1 / |sharpPerronHalfPoint x - (n : ℝ)|
  else 0

private theorem summable_sharpPerronNearWeight (x : ℝ) :
    Summable (sharpPerronNearWeight x) := by
  apply summable_of_ne_finset_zero (s := Finset.range (2 * ⌊x⌋₊ + 2))
  intro n hn
  simp [sharpPerronNearWeight, hn]

private theorem tsum_sharpPerronNearWeight_eq (x : ℝ) :
    (∑' n : ℕ, sharpPerronNearWeight x n) =
      ∑ n ∈ Finset.range (2 * ⌊x⌋₊ + 2),
        1 / |sharpPerronHalfPoint x - (n : ℝ)| := by
  rw [tsum_eq_sum (s := Finset.range (2 * ⌊x⌋₊ + 2))]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [sharpPerronNearWeight, hn]
  · intro n hn
    simp [sharpPerronNearWeight, hn]

private theorem near_mem_halfPoint_range
    {x : ℝ} {n : ℕ}
    (hnUpper : (n : ℝ) < 2 * sharpPerronHalfPoint x) :
    n ∈ Finset.range (2 * ⌊x⌋₊ + 2) := by
  rw [Finset.mem_range]
  rw [sharpPerronHalfPoint] at hnUpper
  have hreal : (n : ℝ) < ((2 * ⌊x⌋₊ + 2 : ℕ) : ℝ) := by
    push_cast at hnUpper ⊢
    linarith
  exact_mod_cast hreal

private theorem tsum_sharpPerronNearWeight_le_harmonic (x : ℝ) :
    (∑' n : ℕ, sharpPerronNearWeight x n) ≤
      4 * (harmonic (⌊x⌋₊ + 1) : ℝ) := by
  rw [tsum_sharpPerronNearWeight_eq]
  simpa only [sharpPerronHalfPoint] using
    sum_range_inv_abs_nat_add_half_le ⌊x⌋₊

/-- Exact global arithmetic estimate before the elementary logarithmic
simplification. -/
theorem norm_optimized_halfPoint_Perron_sub_psi_le_arithmetic
    {T x : ℝ} (hy : 2 ≤ sharpPerronHalfPoint x) (hT : 0 < T) :
    ‖(1 / (2 * Real.pi) : ℂ) *
          (∫ t in (-T)..T,
            (-deriv riemannZeta
                ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                  (t : ℂ) * Complex.I) /
                riemannZeta
                  ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                    (t : ℂ) * Complex.I)) *
              (sharpPerronHalfPoint x : ℂ) ^
                ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                  (t : ℂ) * Complex.I) /
                ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                  (t : ℂ) * Complex.I)) -
        (Chebyshev.psi (sharpPerronHalfPoint x) : ℂ)‖ ≤
      (sharpPerronRatioBound *
          Real.log (2 * sharpPerronHalfPoint x) *
          (2 * sharpPerronHalfPoint x) / (Real.pi * T)) *
          (4 * (harmonic (⌊x⌋₊ + 1) : ℝ)) +
        (2 * (sharpPerronHalfPoint x ^
            sharpPerronAbscissa (sharpPerronHalfPoint x)) /
            (Real.pi * T)) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa (sharpPerronHalfPoint x))) := by
  let y := sharpPerronHalfPoint x
  let c := sharpPerronAbscissa y
  let A := sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
    (Real.pi * T)
  let B := 2 * y ^ c / (Real.pi * T)
  let e : ℕ → ℝ := fun n =>
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel c T y n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronCutoff y n‖
  let d : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c
  let M : ℕ → ℝ := fun n => A * sharpPerronNearWeight x n + B * d n
  have hy0 : 0 < y := by dsimp [y]; linarith
  have hc : 1 < c := by
    exact one_lt_sharpPerronAbscissa (by dsimp [y]; linarith)
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (zero_le_one.trans one_le_sharpPerronRatioBound)
          (Real.log_nonneg (by dsimp [y]; linarith)))
        (by dsimp [y]; positivity)) hpiT.le
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n
    dsimp [d]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hNear0 : ∀ n, 0 ≤ sharpPerronNearWeight x n := by
    intro n
    simp only [sharpPerronNearWeight]
    split_ifs
    · positivity
    · exact le_rfl
  have heSummable : Summable e := by
    exact summable_norm_vonMangoldt_sharpPerron_cutoffError hc hy0
  have hdSummable : Summable d :=
    summable_vonMangoldt_div_nat_rpow hc
  have hMSummable : Summable M := by
    exact ((summable_sharpPerronNearWeight x).mul_left A).add
      (hdSummable.mul_left B)
  have hpoint : ∀ n, e n ≤ M n := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      dsimp [e, M, d]
      simp
      exact mul_nonneg hA0 (hNear0 0)
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      by_cases hnear : y / 2 < (n : ℝ) ∧ (n : ℝ) < 2 * y
      · have hmem := near_mem_halfPoint_range hnear.2
        have hnearBound := norm_vonMangoldt_halfPoint_cutoffError_le_near
          hy hT hn hnear.1 hnear.2
        have hweight : sharpPerronNearWeight x n =
            1 / |y - (n : ℝ)| := by
          simp [sharpPerronNearWeight, hmem, y]
        dsimp [e, M, A, B, d, c, y] at hnearBound ⊢
        rw [hweight]
        exact hnearBound.trans (le_add_of_nonneg_right (mul_nonneg hB0 (hd0 n)))
      · have hfar : (n : ℝ) ≤ y / 2 ∨ 2 * y ≤ (n : ℝ) := by
          by_cases hlow : (n : ℝ) ≤ y / 2
          · exact Or.inl hlow
          · exact Or.inr (le_of_not_gt (fun h => hnear ⟨lt_of_not_ge hlow, h⟩))
        have hfarBound := norm_vonMangoldt_halfPoint_cutoffError_le_far
          hy hT hn hfar
        dsimp [e, M, A, B, d, c, y] at hfarBound ⊢
        exact hfarBound.trans (le_add_of_nonneg_left
          (mul_nonneg hA0 (hNear0 n)))
  calc
    ‖(1 / (2 * Real.pi) : ℂ) *
          (∫ t in (-T)..T,
            (-deriv riemannZeta
                ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                  (t : ℂ) * Complex.I) /
                riemannZeta
                  ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                    (t : ℂ) * Complex.I)) *
              (sharpPerronHalfPoint x : ℂ) ^
                ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                  (t : ℂ) * Complex.I) /
                ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                  (t : ℂ) * Complex.I)) -
        (Chebyshev.psi (sharpPerronHalfPoint x) : ℂ)‖ ≤
      ∑' n : ℕ, e n := by
        exact norm_sharpPerron_logDerivative_sub_psi_le_tsum_termErrors hc hy0
    _ ≤ ∑' n : ℕ, M n :=
      Summable.tsum_mono heSummable hMSummable hpoint
    _ = A * (∑' n : ℕ, sharpPerronNearWeight x n) +
        B * (∑' n : ℕ, d n) := by
      rw [show M = fun n => A * sharpPerronNearWeight x n + B * d n from rfl,
        Summable.tsum_add ((summable_sharpPerronNearWeight x).mul_left A)
          (hdSummable.mul_left B), tsum_mul_left, tsum_mul_left]
    _ ≤ A * (4 * (harmonic (⌊x⌋₊ + 1) : ℝ)) +
        B * (∑' n : ℕ, d n) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (tsum_sharpPerronNearWeight_le_harmonic x) hA0)
        le_rfl
    _ = (sharpPerronRatioBound *
          Real.log (2 * sharpPerronHalfPoint x) *
          (2 * sharpPerronHalfPoint x) / (Real.pi * T)) *
          (4 * (harmonic (⌊x⌋₊ + 1) : ℝ)) +
        (2 * (sharpPerronHalfPoint x ^
            sharpPerronAbscissa (sharpPerronHalfPoint x)) /
            (Real.pi * T)) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa (sharpPerronHalfPoint x))) := rfl

end GafniTao

import GafniTao.SharpExplicitFormula

/-!
# Reduction of the short-interval formula to the sharp psi formula

This file isolates the classical Chapter 17 theorem at one endpoint and
proves, in Lean, the exact subtraction that produces the Gafni--Tao
short-interval formula.  The remaining upstream theorem is now the standard
sharp truncation for `Chebyshev.psi`, not a bespoke exceptional-set claim.
-/

open scoped BigOperators

namespace GafniTao

/-- The multiplicity-weighted truncated nontrivial-zero term in the classical
explicit formula for `psi(x)`. -/
noncomputable def truncatedPsiZeroSum (T x : ℝ) : ℂ :=
  ∑ rho ∈ zeroSet 0 T,
    (zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)

/-- The classical sharp-truncation remainder with the analytic sign
`psi(x)-x = -sum_rho x^rho/rho + error`. -/
noncomputable def sharpPsiTruncationError (T x : ℝ) : ℂ :=
  (((Chebyshev.psi x - x : ℝ) : ℂ) + truncatedPsiZeroSum T x)

/-- Davenport Chapter 17 in the application range `2 ≤ T ≤ x`, with
the endpoint term absorbed into the displayed error. -/
def SharpPsiTruncationBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {T x : ℝ}, 2 ≤ T → T ≤ x → 2 ≤ x →
    ‖sharpPsiTruncationError T x‖ ≤ C * x * (Real.log x) ^ 2 / T

theorem truncatedPsiZeroSum_sub_eq_fullZeroIncrementSum
    (T tau x : ℝ) :
    truncatedPsiZeroSum T (x + x / tau) - truncatedPsiZeroSum T x =
      fullZeroIncrementSum T tau x := by
  unfold truncatedPsiZeroSum fullZeroIncrementSum zeroIncrementTerm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  ring

/-- Exact endpoint subtraction, including the Chebyshev half-open interval
convention. -/
theorem sharpExplicitFormulaError_eq_endpoint_sub
    {T tau x : ℝ} (hx : 0 ≤ x) (htau : 0 < tau) :
    sharpExplicitFormulaError T tau x =
      sharpPsiTruncationError T (x + x / tau) -
        sharpPsiTruncationError T x := by
  have hy : 0 ≤ x / tau := div_nonneg hx htau.le
  rw [sharpExplicitFormulaError, mangoldtIntervalSum_eq_psi_sub x hy]
  simp only [sharpPsiTruncationError]
  rw [← truncatedPsiZeroSum_sub_eq_fullZeroIncrementSum]
  push_cast
  ring

/-- The standard one-endpoint sharp psi theorem implies the exact
short-interval contract used by the Gafni--Tao consumer. -/
theorem sharpTruncatedExplicitFormulaBound_of_sharpPsi
    (hPsi : SharpPsiTruncationBound) :
    SharpTruncatedExplicitFormulaBound := by
  rcases hPsi with ⟨C, hC, hPsi⟩
  refine ⟨9 * C, mul_pos (by norm_num) hC, ?_⟩
  intro T tau x htau hT hTx hx
  have hxPos : 0 < x := by linarith
  have htauPos : 0 < tau := zero_lt_one.trans_le htau
  have hyNonneg : 0 ≤ x / tau := div_nonneg hxPos.le htauPos.le
  have hUpper : x + x / tau ≤ 2 * x := by
    have hdiv : x / tau ≤ x := (div_le_iff₀ htauPos).2 (by
      nlinarith)
    linarith
  have hTUpper : T ≤ x + x / tau := hTx.trans (le_add_of_nonneg_right hyNonneg)
  have hTwoUpper : 2 ≤ x + x / tau := hx.trans (le_add_of_nonneg_right hyNonneg)
  have hAtUpper := hPsi hT hTUpper hTwoUpper
  have hAtLower := hPsi hT hTx hx
  rw [sharpExplicitFormulaError_eq_endpoint_sub hxPos.le htauPos]
  refine (norm_sub_le _ _).trans ?_
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogUpper : Real.log (x + x / tau) ≤ 2 * Real.log x := by
    calc
      Real.log (x + x / tau) ≤ Real.log (2 * x) := by
        exact Real.strictMonoOn_log.monotoneOn
          (add_pos_of_pos_of_nonneg hxPos hyNonneg)
          (mul_pos (by norm_num) hxPos) hUpper
      _ = Real.log 2 + Real.log x := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxPos.ne']
      _ ≤ 2 * Real.log x := by
        have : Real.log 2 ≤ Real.log x :=
          Real.strictMonoOn_log.monotoneOn (by norm_num) hxPos hx
        linarith
  have hlogSq : (Real.log (x + x / tau)) ^ 2 ≤
      4 * (Real.log x) ^ 2 := by
    have hlogUpperNonneg : 0 ≤ Real.log (x + x / tau) :=
      Real.log_nonneg (by linarith)
    nlinarith
  have hUpperError :
      ‖sharpPsiTruncationError T (x + x / tau)‖ ≤
        8 * C * x * (Real.log x) ^ 2 / T := by
    calc
      ‖sharpPsiTruncationError T (x + x / tau)‖ ≤
          C * (x + x / tau) * (Real.log (x + x / tau)) ^ 2 / T := hAtUpper
      _ ≤ C * (2 * x) * (4 * (Real.log x) ^ 2) / T := by
        apply div_le_div_of_nonneg_right
        · gcongr
        · linarith
      _ = 8 * C * x * (Real.log x) ^ 2 / T := by ring
  calc
    ‖sharpPsiTruncationError T (x + x / tau)‖ +
        ‖sharpPsiTruncationError T x‖
      ≤ 8 * C * x * (Real.log x) ^ 2 / T +
          C * x * (Real.log x) ^ 2 / T := add_le_add hUpperError hAtLower
    _ = (9 * C) * x * (Real.log x) ^ 2 / T := by ring

end GafniTao

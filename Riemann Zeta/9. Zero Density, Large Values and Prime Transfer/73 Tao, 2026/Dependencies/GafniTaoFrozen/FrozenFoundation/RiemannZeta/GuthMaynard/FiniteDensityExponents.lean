import RiemannZeta.GuthMaynard.InghamBound

namespace RiemannZeta.GuthMaynard

/-!
# Arithmetic for the finite classical density transfer

These lemmas isolate the exact range comparisons used when the finite
large-values estimates are specialized to the Ingham and Huxley endpoints.
They resolve only the exceptional short zeta-polynomial alternative: that
range is empty for Ingham and for the lower part of Huxley's interval, while
the proved Weyl threshold covers the remaining Huxley range.  They do not
remove the distinct medium ordinary-zeta Type-I reflection in ANTEDB Lemma
11.5.
-/

/-- In the interior of Ingham's interval, the upper end of the
zeta-polynomial range is strictly below its lower end `2`. -/
theorem ingham_zeta_polynomial_range_empty
    {σ τ : ℝ} (hσ : 1 / 2 < σ) (hτ : 2 ≤ τ) :
    ¬ τ < 4 * (2 - σ) / 3 := by
  intro hUpper
  nlinarith

/-- Through `σ = 5/6`, Huxley's zeta-polynomial range is empty. -/
theorem huxley_zeta_polynomial_range_empty
    {σ τ : ℝ} (hσ : σ ≤ 5 / 6) (hτ : 2 ≤ τ) :
    ¬ τ < 4 * (3 * σ - 1) / 3 := by
  intro hUpper
  nlinarith

/-- Above `σ = 5/6`, every exponent in Huxley's zeta-polynomial range lies
strictly below the Weyl-exclusion threshold `6σ-3`. -/
theorem huxley_zeta_polynomial_range_below_weyl
    {σ τ : ℝ} (hσ : 5 / 6 < σ)
    (hτ : τ < 4 * (3 * σ - 1) / 3) :
    τ < 6 * σ - 3 := by
  nlinarith

/-- The Huxley and Ingham endpoint exponents coincide at `σ = 3/4`. -/
theorem classical_density_exponents_eq_at_three_quarters :
    3 * (1 - (3 / 4 : ℝ)) / (2 - 3 / 4) =
      3 * (1 - (3 / 4 : ℝ)) / (3 * (3 / 4 : ℝ) - 1) := by
  norm_num

end RiemannZeta.GuthMaynard

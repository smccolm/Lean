import Dubon2026.GammaDualMellinTerm

/-! # Justified finite-contour transform at an arbitrary positive conductor -/

namespace Dubon2026

open Complex MeasureTheory

noncomputable section

/-- The true Riesz Gamma symbol is continuous on the whole left contour line. -/
theorem continuous_gammaRieszSymbol_left {k : ℝ} (hk : 2 ≤ k) :
    Continuous (fun t : ℝ => gammaRieszSymbol k 2 (gammaVerticalPoint (-1 / 8) t)) := by
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using
    continuous_rankinPerron_reflected_weight hk (a := 1) (x := 1) (by norm_num) (by norm_num)

/-- The actual positive-conductor Mellin weight is continuous at all finite heights. -/
theorem continuous_positive_conductor_mellin_weight {k A x : ℝ}
    (hk : 2 ≤ k) (hA : 0 < A) (hx : 0 < x) :
    Continuous (fun t : ℝ => (x : ℂ) ^ (gammaVerticalPoint (-1 / 8) t + 2) *
      (A : ℂ) ^ (gammaVerticalPoint (-1 / 8) t) * gammaRieszSymbol k 2 (gammaVerticalPoint (-1 / 8) t)) := by
  have hpx : Continuous (fun t : ℝ => (x : ℂ) ^ (gammaVerticalPoint (-1 / 8) t + 2)) :=
    continuous_const.cpow (by unfold gammaVerticalPoint; fun_prop) (fun _ => Or.inl hx)
  have hpA : Continuous (fun t : ℝ => (A : ℂ) ^ (gammaVerticalPoint (-1 / 8) t)) :=
    continuous_const.cpow (by unfold gammaVerticalPoint; fun_prop) (fun _ => Or.inl hA)
  exact (hpx.mul hpA).mul (continuous_gammaRieszSymbol_left hk)

/-- Actual absolute Dirichlet convergence justifies the coefficient/Gamma transform at every finite vertical cutoff. -/
theorem positive_conductor_mellin_cutoff_eq_series (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((9 / 8 : ℝ) : ℂ)) {k A x : ℝ}
    (hk : 2 ≤ k) (hA : 0 < A) (hx : 0 < x) (T : ℝ) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t in -T..T,
      ((x : ℂ) ^ (gammaVerticalPoint (-1 / 8) t + 2) *
        (A : ℂ) ^ (gammaVerticalPoint (-1 / 8) t) * gammaRieszSymbol k 2 (gammaVerticalPoint (-1 / 8) t)) *
          LSeries (fun n => (a n : ℂ)) (1 - gammaVerticalPoint (-1 / 8) t)) =
      ∑' n : ℕ, gammaRieszDualCutoffTerm a k A x T n := by
  have hs := hasSum_intervalIntegral_mul_LSeries ha
    (z := fun t => 1 - gammaVerticalPoint (-1 / 8) t)
    (u := -T) (v := T) (by unfold gammaVerticalPoint; fun_prop)
    (by intro t _; norm_num [gammaVerticalPoint_re])
    (continuous_positive_conductor_mellin_weight hk hA hx).continuousOn
  have hn := hs.const_smul (1 / (2 * Real.pi) : ℝ)
  have hn' : HasSum (fun n : ℕ => gammaRieszDualCutoffTerm a k A x T n)
      ((1 / (2 * Real.pi) : ℝ) • (∫ t in -T..T,
        ((x : ℂ) ^ (gammaVerticalPoint (-1 / 8) t + 2) *
          (A : ℂ) ^ (gammaVerticalPoint (-1 / 8) t) * gammaRieszSymbol k 2 (gammaVerticalPoint (-1 / 8) t)) *
            LSeries (fun n => (a n : ℂ)) (1 - gammaVerticalPoint (-1 / 8) t))) := by
    convert hn using 1
    funext n
    exact (coefficient_reflected_mellin_term_integral a ha0 k hA hx T n).symm
  exact hn'.tsum_eq.symm

end
end Dubon2026

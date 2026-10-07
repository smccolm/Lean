import Dubon2026.PrimitiveLatticeScaling

/-! # Exact full-lattice to primitive Eisenstein series decomposition -/

namespace Dubon2026

open UpperHalfPlane EisensteinSeries

noncomputable section

/-- Each genuine nonzero gcd fiber sums to its dilation factor times the primitive-row sum. -/
theorem tsum_nonholomorphicEisensteinTerm_gcd {s : ℂ} (hs : 1 < s.re) (z : ℍ) (n : ℕ) :
    (∑' v : gammaSet 1 n 0, nonholomorphicEisensteinTerm s v.val z) =
      (n : ℂ) ^ (-(2 * s)) * ∑' v : gammaSet 1 1 0, nonholomorphicEisensteinTerm s v.val z := by
  by_cases hn : n = 0
  · subst n
    have hsne : s ≠ 0 := by
      intro h
      simp only [h, Complex.zero_re] at hs
      linarith
    have hs0 : -(2 * s) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (by norm_num) hsne)
    simp only [nonholomorphicEisensteinTerm_gcd, Complex.zero_cpow hs0, Nat.cast_zero,
      zero_mul, tsum_zero]
  · letI : NeZero n := ⟨hn⟩
    have he : (∑' v : gammaSet 1 n 0, nonholomorphicEisensteinTerm s v.val z) =
        ∑' v : gammaSet 1 n 0, (n : ℂ) ^ (-(2 * s)) *
          nonholomorphicEisensteinTerm s (divIntMap n v.val) z :=
      tsum_congr (fun v => nonholomorphicEisensteinTerm_gcd s z v)
    rw [he, tsum_mul_left]
    congr 1
    simpa only [gammaSetDivGcdEquiv_eq] using
      (gammaSetDivGcdEquiv n).tsum_eq (fun v => nonholomorphicEisensteinTerm s v.val z)

/-- Reindexing by the actual integer gcd extracts the scalar Dirichlet series exactly. -/
theorem tsum_nonholomorphicEisensteinTerm_primitive {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    (∑' v : Fin 2 → ℤ, nonholomorphicEisensteinTerm s v z) =
      (∑' n : ℕ, (n : ℂ) ^ (-(2 * s))) *
        ∑' v : gammaSet 1 1 0, nonholomorphicEisensteinTerm s v.val z := by
  have hh : Summable (fun v : Σ n : ℕ, gammaSet 1 n 0 => nonholomorphicEisensteinTerm s v.2.val z) := by
    simpa only [gammaSetDivGcdSigmaEquiv_symm_eq] using
      gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr
        (summable_norm_nonholomorphicEisensteinTerm hs z).of_norm
  rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq]
  simp only [gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [hh.tsum_sigma]
  exact (tsum_congr (fun n => tsum_nonholomorphicEisensteinTerm_gcd hs z n)).trans
    (tsum_mul_right)

/-- The exact extracted scalar is the actual Riemann zeta value at 2s. -/
theorem tsum_nonholomorphicEisensteinTerm_zeta {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    (∑' v : Fin 2 → ℤ, nonholomorphicEisensteinTerm s v z) =
      riemannZeta (2 * s) * (2 * gamma0Eisenstein 1 s z) := by
  have h2 : 1 < (2 * s).re := by simp only [two_mul, Complex.add_re]; linarith
  rw [tsum_nonholomorphicEisensteinTerm_primitive hs z,
    zeta_eq_tsum_one_div_nat_cpow h2]
  simp_rw [Complex.cpow_neg, one_div]
  rw [gamma0Eisenstein, gamma0PrimitiveRows_one_eq]
  ring

end
end Dubon2026

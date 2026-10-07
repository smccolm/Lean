import Dubon2026.PrimitiveLatticeSum

/-! # The actual completed Epstein series and primitive full-level Eisenstein series -/

namespace Dubon2026

open UpperHalfPlane

noncomputable section

/-- The literal lattice quadratic kernel is exactly the genuine nonholomorphic row kernel. -/
theorem latticeEpstein_term_eq_eisenstein (z : ℍ) (s : ℂ) (v : ℤ × ℤ) :
    1 / (latticeQuadratic z v : ℂ) ^ s =
      nonholomorphicEisensteinTerm s ((finTwoArrowEquiv ℤ).symm v) z := by
  rw [nonholomorphicEisensteinTerm, eisensteinRowHeight_pair_inv, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (latticeQuadratic_nonneg z v)]
      exact Real.pi_ne_zero.symm), one_div]

/-- The zero lattice row contributes nothing in the convergent half-plane. -/
theorem latticeEpstein_full_sum (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    (∑' v : Fin 2 → ℤ, nonholomorphicEisensteinTerm s v z) = 2 * latticeEpsteinSeries z s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith
  have he : (∑' v : {v : ℤ × ℤ // v ≠ 0}, 1 / (latticeQuadratic z v.val : ℂ) ^ s) =
      ∑' v : ℤ × ℤ, 1 / (latticeQuadratic z v : ℂ) ^ s := by
    change (∑' v : {v : ℤ × ℤ | v ≠ 0}, 1 / (latticeQuadratic z v.val : ℂ) ^ s) = _
    apply tsum_subtype_eq_of_support_subset (s := {v : ℤ × ℤ | v ≠ 0})
      (f := fun v : ℤ × ℤ => 1 / (latticeQuadratic z v : ℂ) ^ s)
    intro v hv
    change v ≠ 0
    intro h
    subst v
    simp [Function.mem_support, latticeQuadratic, Complex.zero_cpow hs0] at hv
  rw [latticeEpsteinSeries, he, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  simp_rw [latticeEpstein_term_eq_eisenstein]
  ring

/-- The full lattice decomposes exactly into primitive rows and the actual zeta factor. -/
theorem latticeEpsteinSeries_eq_zeta_eisenstein (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    latticeEpsteinSeries z s = riemannZeta (2 * s) * gamma0Eisenstein 1 s z := by
  have h := tsum_nonholomorphicEisensteinTerm_zeta hs z
  rw [latticeEpstein_full_sum z hs] at h
  linear_combination h / 2

/-- The proved lattice continuation supplies the actual completed full-level primitive Eisenstein series. -/
theorem latticeCompletedMellin_eq_completed_eisenstein (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    latticeCompletedMellin z s =
      ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s)) * gamma0Eisenstein 1 s z := by
  rw [latticeCompletedMellin_eq_epstein z hs, latticeEpsteinSeries_eq_zeta_eisenstein z hs]
  ring

end
end Dubon2026

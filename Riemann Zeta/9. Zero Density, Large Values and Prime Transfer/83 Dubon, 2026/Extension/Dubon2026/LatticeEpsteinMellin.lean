import Dubon2026.LatticeCompletedMellin
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-! # The actual Epstein lattice series and its completed Mellin continuation -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set

noncomputable section

/-- The literal nonzero lattice Epstein half-sum, normalized by the covolume-one quadratic form. -/
def latticeEpsteinSeries (z : ℍ) (s : ℂ) : ℂ :=
  (∑' v : {v : ℤ × ℤ // v ≠ 0}, 1 / (latticeQuadratic z v.val : ℂ) ^ s) / 2

/-- The actual primitive-row height kernel and the determinant-one quadratic form are reciprocal. -/
theorem eisensteinRowHeight_pair_inv (z : ℍ) (v : ℤ × ℤ) :
    eisensteinRowHeight ((finTwoArrowEquiv ℤ).symm v) z = (latticeQuadratic z v)⁻¹ := by
  rw [latticeQuadratic_eq_norm, inv_div, eisensteinRowHeight]
  rfl

/-- The genuine quadratic lattice Dirichlet series is summable throughout its real convergence half-plane. -/
theorem summable_latticeQuadratic_inverse_rpow (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun v : ℤ × ℤ => 1 / (latticeQuadratic z v) ^ σ) := by
  have h := (summable_norm_nonholomorphicEisensteinTerm (s := (σ : ℂ)) hσ z).comp_injective
    (finTwoArrowEquiv ℤ).symm.injective
  apply h.congr
  intro v
  dsimp only [Function.comp_apply]
  rw [nonholomorphicEisensteinTerm,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (eisensteinRowHeight_nonneg _ z)
      (by simpa only [Complex.ofReal_re] using (ne_of_gt (lt_trans zero_lt_one hσ))),
    eisensteinRowHeight_pair_inv, Complex.ofReal_re,
    Real.inv_rpow (latticeQuadratic_nonneg z v), one_div]

/-- The actual nonzero lattice series is absolutely convergent for Re(s)>1. -/
theorem summable_norm_latticeEpstein (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : {v : ℤ × ℤ // v ≠ 0} => ‖1 / (latticeQuadratic z v.val : ℂ) ^ s‖) := by
  have h := (summable_latticeQuadratic_inverse_rpow z hs).subtype {v | v ≠ 0}
  apply h.congr
  intro v
  dsimp only [Function.comp_apply]
  rw [norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos
    (lt_of_lt_of_le (latticeQuadraticLower_pos z) (latticeQuadratic_lower_nonzero z v.property))]

/-- The actual theta remainder is the exponential series required by the Mellin-to-Dirichlet theorem. -/
theorem hasSum_latticeTheta_exponentials (z : ℍ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun v : {v : ℤ × ℤ // v ≠ 0} =>
      (1 : ℂ) * (Real.exp (-Real.pi * latticeQuadratic z v.val * t) : ℂ))
      (latticeThetaRemainder z t : ℂ) := by
  have h := Complex.hasSum_ofReal.mpr (summable_latticeThetaRemainder z ht).hasSum
  apply h.congr_fun
  intro v
  simp only [one_mul, latticeThetaTerm]
  congr 2
  ring

/-- The meromorphic theta continuation equals the literal completed Epstein half-sum in Re(s)>1. -/
theorem latticeCompletedMellin_eq_epstein (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    latticeCompletedMellin z s =
      ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) * latticeEpsteinSeries z s := by
  have h := hasSum_mellin_pi_mul
    (a := fun _ : {v : ℤ × ℤ // v ≠ 0} => (1 : ℂ))
    (q := fun v : {v : ℤ × ℤ // v ≠ 0} => latticeQuadratic z v.val)
    (F := fun t : ℝ => (latticeThetaRemainder z t : ℂ))
    (fun v => Or.inr (lt_of_lt_of_le (latticeQuadraticLower_pos z)
      (latticeQuadratic_lower_nonzero z v.property)))
    (lt_trans zero_lt_one hs) (fun _ ht => hasSum_latticeTheta_exponentials z ht)
    (by simpa only [norm_one] using
      (summable_latticeQuadratic_inverse_rpow z hs).subtype {v | v ≠ 0})
  rw [latticeCompletedMellin_eq_integral z hs]
  change mellin (fun t : ℝ => (latticeThetaRemainder z t : ℂ)) s / 2 = _
  rw [← h.tsum_eq, latticeEpsteinSeries]
  simp only [mul_one, div_eq_mul_inv, one_mul]
  rw [tsum_mul_left]
  ring

end
end Dubon2026

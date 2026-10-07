import Dubon2026.LatticeMellinMajorant

/-! # Explicit geometric majorants for the actual Epstein lattice series -/

namespace Dubon2026

open UpperHalfPlane

noncomputable section

/-- At the actual point i, the determinant-one quadratic form is the ordinary sum of two squares. -/
theorem latticeQuadratic_I (v : ℤ × ℤ) :
    latticeQuadratic UpperHalfPlane.I v = (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
  simp [latticeQuadratic, UpperHalfPlane.I_re, UpperHalfPlane.I_im, add_comm]

/-- The fixed reference-lattice majorant converges in the actual Epstein convergence range. -/
theorem summable_reference_lattice {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun v : {v : ℤ × ℤ // v ≠ 0} =>
      1 / ((v.val.1 : ℝ) ^ 2 + (v.val.2 : ℝ) ^ 2) ^ σ) := by
  simpa only [latticeQuadratic_I] using
    (summable_latticeQuadratic_inverse_rpow UpperHalfPlane.I hσ).subtype {v | v ≠ 0}

/-- The proved lower quadratic bound gives a literal reference-lattice majorant term by term. -/
theorem latticeQuadratic_inverse_rpow_le (z : ℍ) {σ : ℝ} (hσ : 0 ≤ σ)
    (v : {v : ℤ × ℤ // v ≠ 0}) :
    1 / (latticeQuadratic z v.val) ^ σ ≤
      (latticeQuadraticLower z) ^ (-σ) *
        (1 / ((v.val.1 : ℝ) ^ 2 + (v.val.2 : ℝ) ^ 2) ^ σ) := by
  have hv : 0 < (v.val.1 : ℝ) ^ 2 + (v.val.2 : ℝ) ^ 2 :=
    lt_of_lt_of_le zero_lt_one (one_le_lattice_sq v.property)
  have hl := Real.rpow_le_rpow
    (mul_nonneg (latticeQuadraticLower_pos z).le hv.le) (latticeQuadratic_lower z v.val) hσ
  have h := one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos (mul_pos (latticeQuadraticLower_pos z) hv) σ) hl
  rw [Real.mul_rpow (latticeQuadraticLower_pos z).le hv.le] at h
  simpa only [Real.rpow_neg (latticeQuadraticLower_pos z).le, div_eq_mul_inv,
    one_mul, mul_inv_rev, mul_comm, mul_one] using h

/-- The genuine complex Epstein half-sum has an explicit geometric bound uniform on each vertical line. -/
theorem norm_latticeEpsteinSeries_le (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    ‖latticeEpsteinSeries z s‖ ≤ (latticeQuadraticLower z) ^ (-s.re) *
      (∑' v : {v : ℤ × ℤ // v ≠ 0},
        1 / ((v.val.1 : ℝ) ^ 2 + (v.val.2 : ℝ) ^ 2) ^ s.re) / 2 := by
  have hn := summable_norm_latticeEpstein z hs
  have hm := (summable_reference_lattice hs).mul_left ((latticeQuadraticLower z) ^ (-s.re))
  have hle : (∑' v : {v : ℤ × ℤ // v ≠ 0}, ‖1 / (latticeQuadratic z v.val : ℂ) ^ s‖) ≤
      (latticeQuadraticLower z) ^ (-s.re) *
        (∑' v : {v : ℤ × ℤ // v ≠ 0},
          1 / ((v.val.1 : ℝ) ^ 2 + (v.val.2 : ℝ) ^ 2) ^ s.re) := by
    rw [← tsum_mul_left]
    apply hn.tsum_le_tsum _ hm
    intro v
    rw [norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le (latticeQuadraticLower_pos z) (latticeQuadratic_lower_nonzero z v.property))]
    exact latticeQuadratic_inverse_rpow_le z (le_of_lt (lt_trans zero_lt_one hs)) v
  rw [latticeEpsteinSeries, norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right ((norm_tsum_le_tsum_norm hn).trans hle) (by norm_num)

end
end Dubon2026

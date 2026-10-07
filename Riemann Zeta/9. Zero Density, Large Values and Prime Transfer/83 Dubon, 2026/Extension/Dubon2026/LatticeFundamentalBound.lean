import Dubon2026.LatticeEpsteinMajorant
import Dubon2026.LatticeEpsteinPrimitive
import Dubon2026.ModularPeterssonMeasure

/-! # Genuine modular-domain growth bounds for the completed lattice series -/

namespace Dubon2026

open UpperHalfPlane ModularGroup
open scoped MatrixGroups

noncomputable section

/-- On the actual standard modular domain the reciprocal quadratic lower bound is at most 4y. -/
theorem latticeQuadraticLower_inv_le_of_mem_fd {z : ℍ} (hz : z ∈ fd) :
    (latticeQuadraticLower z)⁻¹ ≤ 4 * z.im := by
  rw [latticeQuadraticLower, inv_div, div_le_iff₀ z.im_pos]
  have hx := abs_le.mp hz.2
  have hy := three_le_four_mul_im_sq_of_mem_fd hz
  nlinarith

/-- The actual geometric Epstein majorant grows at most like a power of height on the standard domain. -/
theorem latticeQuadraticLower_rpow_le_of_mem_fd {z : ℍ} (hz : z ∈ fd) {σ : ℝ} (hσ : 0 ≤ σ) :
    (latticeQuadraticLower z) ^ (-σ) ≤ (4 : ℝ) ^ σ * z.im ^ σ := by
  rw [Real.rpow_neg (latticeQuadraticLower_pos z).le, ← Real.inv_rpow (latticeQuadraticLower_pos z).le]
  have h := Real.rpow_le_rpow (inv_nonneg.mpr (latticeQuadraticLower_pos z).le)
    (latticeQuadraticLower_inv_le_of_mem_fd hz) hσ
  simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) z.im_pos.le] using h

/-- The literal Epstein series has a uniform polynomial height bound throughout the true modular domain. -/
theorem exists_latticeEpsteinSeries_bound_fd {s : ℂ} (hs : 1 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ fd, ‖latticeEpsteinSeries z s‖ ≤ C * z.im ^ s.re := by
  let S : ℝ := ∑' v : {v : ℤ × ℤ // v ≠ 0},
    1 / ((v.val.1 : ℝ) ^ 2 + (v.val.2 : ℝ) ^ 2) ^ s.re
  have hS : 0 ≤ S := tsum_nonneg (fun _ => by positivity)
  refine ⟨1 + (4 : ℝ) ^ s.re * S / 2, by positivity, ?_⟩
  intro z hz
  have h1 := norm_latticeEpsteinSeries_le z hs
  have h2 := mul_le_mul_of_nonneg_right
    (latticeQuadraticLower_rpow_le_of_mem_fd hz (le_of_lt (lt_trans zero_lt_one hs))) hS
  have hy : 0 < z.im ^ s.re := Real.rpow_pos_of_pos z.im_pos _
  change ‖latticeEpsteinSeries z s‖ ≤ (1 + (4 : ℝ) ^ s.re * S / 2) * z.im ^ s.re
  change ‖latticeEpsteinSeries z s‖ ≤ (latticeQuadraticLower z) ^ (-s.re) * S / 2 at h1
  nlinarith

/-- The actual completed lattice Mellin value has a polynomial height bound in its convergence half-plane. -/
theorem exists_latticeCompletedMellin_bound_fd {s : ℂ} (hs : 1 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ fd, ‖latticeCompletedMellin z s‖ ≤ C * z.im ^ s.re := by
  obtain ⟨C, hC, hb⟩ := exists_latticeEpsteinSeries_bound_fd hs
  refine ⟨1 + ‖(Real.pi : ℂ) ^ (-s) * Complex.Gamma s‖ * C, by positivity, ?_⟩
  intro z hz
  rw [latticeCompletedMellin_eq_epstein z hs, norm_mul]
  have h := mul_le_mul_of_nonneg_left (hb z hz)
    (norm_nonneg ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s))
  have hy : 0 < z.im ^ s.re := Real.rpow_pos_of_pos z.im_pos _
  nlinarith

/-- The genuine convergent Epstein series is invariant under every actual integer modular transformation. -/
theorem latticeEpsteinSeries_SL2 {s : ℂ} (hs : 1 < s.re) (z : ℍ) (A : SL(2, ℤ)) :
    latticeEpsteinSeries (A • z) s = latticeEpsteinSeries z s := by
  rw [latticeEpsteinSeries_eq_zeta_eisenstein _ hs, latticeEpsteinSeries_eq_zeta_eisenstein _ hs,
    gamma0Eisenstein_invariant 1 s z A (by
      apply CongruenceSubgroup.Gamma0_mem.mpr
      exact Subsingleton.elim _ _)]

/-- The actual completed positive-lattice majorant is modular invariant in its convergence half-plane. -/
theorem latticeCompletedMellin_SL2 {s : ℂ} (hs : 1 < s.re) (z : ℍ) (A : SL(2, ℤ)) :
    latticeCompletedMellin (A • z) s = latticeCompletedMellin z s := by
  rw [latticeCompletedMellin_eq_epstein _ hs, latticeCompletedMellin_eq_epstein _ hs,
    latticeEpsteinSeries_SL2 hs]

end
end Dubon2026

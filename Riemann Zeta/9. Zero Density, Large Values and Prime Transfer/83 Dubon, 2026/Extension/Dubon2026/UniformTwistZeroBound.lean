import Dubon2026.JensenZeroBound
import Dubon2026.ZeroFreeHalfPlanes

/-! # A zero-count bound uniform over the compact family of actual prime twists -/

namespace Dubon2026

open Filter Set Complex Metric
open scoped Topology BigOperators

theorem exists_uniform_bohr_lower_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    ∃ c δ : ℝ, 0 < δ ∧ ∀ z, δ ≤ ‖bohrOnTorus a N c z‖ := by
  let g := a 1 • UnitAddTorus.mFourier (primeExponent N 1)
  have hg (z : PrimeTorus N) : ‖g z‖ = ‖a 1‖ := by
    simp only [g, ContinuousMap.smul_apply, smul_eq_mul, norm_mul, norm_mFourier_apply, mul_one]
  have hδ : 0 < ‖a 1‖ / 2 := half_pos (norm_pos_iff.mpr ha)
  obtain ⟨c, hc⟩ := ((Metric.tendsto_nhds.mp (tendsto_bohrOnTorus_atTop a hN)) _ hδ).exists
  refine ⟨c, ‖a 1‖ / 2, hδ, ?_⟩
  intro z
  have hp := ((bohrOnTorus a N c - g).norm_coe_le_norm z).trans_lt
    (show ‖bohrOnTorus a N c - g‖ < ‖a 1‖ / 2 by simpa only [dist_eq_norm] using hc)
  have hr := norm_sub_norm_le (g z) (bohrOnTorus a N c z)
  rw [hg, norm_sub_rev] at hr
  change ‖bohrOnTorus a N c z - g z‖ < ‖a 1‖ / 2 at hp
  linarith

theorem norm_twistedCoefficients (a : ℕ → ℂ) (N : ℕ) (z : PrimeTorus N) (n : ℕ) :
    ‖twistedCoefficients a N z n‖ = ‖a n‖ := by
  rw [twistedCoefficients, bohrMonomial_eq_mFourier, norm_mul, norm_mFourier_apply, mul_one]

theorem twisted_dirichletSum_real (a : ℕ → ℂ) (N : ℕ) (z : PrimeTorus N) (c : ℝ) :
    dirichletSum (twistedCoefficients a N z) N c = bohrOnTorus a N c z := by
  have hzero : primeTorusFlow N 0 = 0 := by
    ext p
    simp [primeTorusFlow]
  have h := verticalFamily_eq_torus_translate a N c z 0
  simpa only [verticalFamily, Complex.ofReal_zero, mul_zero, add_zero, hzero] using h

theorem exists_uniform_twist_ball_zero_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    ∃ c : ℝ, ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : PrimeTorus N) (S : Finset ℂ),
        (∀ s ∈ S, s ∈ closedBall (c : ℂ) r ∧
          dirichletSum (twistedCoefficients a N z) N s = 0) →
        (∑ s ∈ S, (zeroMultiplicity (twistedCoefficients a N z) N s : ℝ)) ≤ C := by
  obtain ⟨c, δ, hδ, hc⟩ := exists_uniform_bohr_lower_bound hN ha
  refine ⟨c, ?_⟩
  intro r hr
  let B := max 1 (∑ n ∈ Finset.Icc 1 N,
    ‖a n‖ * Real.exp (-(c - 2 * r) * Real.log n))
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  refine ⟨max 0 (Real.log (B / δ) / Real.log 2), le_max_left _ _, ?_⟩
  intro z S hS
  have ha' : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
  have hcenter : δ ≤ ‖dirichletSum (twistedCoefficients a N z) N (c : ℂ)‖ := by
    rw [twisted_dirichletSum_real]
    exact hc z
  have hn : 0 < ‖dirichletSum (twistedCoefficients a N z) N (c : ℂ)‖ := hδ.trans_le hcenter
  have hbound := sum_zeroMultiplicity_le_jensen hN ha' hr (show r < 2 * r by linarith)
    hB (norm_pos_iff.mp hn) hS (B := B) (R := 2 * r) (fun s hs => ?_)
  · have he : 2 * r / r = (2 : ℝ) := by field_simp
    rw [he] at hbound
    apply hbound.trans
    apply le_trans _ (le_max_right _ _)
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    exact Real.log_le_log (div_pos hBpos hn)
      (div_le_div_of_nonneg_left hBpos.le hδ hcenter)
  · apply (norm_dirichletSum_le_ball_majorant _ N (sphere_subset_closedBall hs)).trans
    simp only [Complex.ofReal_re, norm_twistedCoefficients]
    exact le_max_right _ _

end Dubon2026

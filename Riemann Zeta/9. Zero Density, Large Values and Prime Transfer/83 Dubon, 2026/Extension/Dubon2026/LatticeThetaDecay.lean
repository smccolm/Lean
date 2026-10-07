import Dubon2026.LatticeThetaPoisson

/-! # Exponential decay of the actual nonzero lattice theta tail -/

namespace Dubon2026

open UpperHalfPlane

noncomputable section

/-- The actual theta remainder sums precisely the nonzero integer rows. -/
def latticeThetaRemainder (z : ℍ) (t : ℝ) : ℝ :=
  ∑' v : {v : ℤ × ℤ // v ≠ 0}, latticeThetaTerm z t v.val

/-- Every nonzero integer row has Euclidean squared length at least one. -/
theorem one_le_lattice_sq {v : ℤ × ℤ} (hv : v ≠ 0) :
    1 ≤ (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
  by_cases h : v.1 = 0
  · have h' : v.2 ≠ 0 := by
      intro h'
      exact hv (Prod.ext h h')
    have hh : (1 : ℝ) ≤ (v.2 : ℝ) ^ 2 := by
      exact_mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs h')
    nlinarith [sq_nonneg (v.1 : ℝ)]
  · have hh : (1 : ℝ) ≤ (v.1 : ℝ) ^ 2 := by
      exact_mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs h)
    nlinarith [sq_nonneg (v.2 : ℝ)]

/-- The actual nonzero lattice spectrum has a strictly positive lower bound. -/
theorem latticeQuadratic_lower_nonzero (z : ℍ) {v : ℤ × ℤ} (hv : v ≠ 0) :
    latticeQuadraticLower z ≤ latticeQuadratic z v := by
  have h := mul_le_mul_of_nonneg_left (one_le_lattice_sq hv) (latticeQuadraticLower_pos z).le
  calc
    latticeQuadraticLower z = latticeQuadraticLower z * 1 := by ring
    _ ≤ latticeQuadraticLower z * ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) := h
    _ ≤ latticeQuadratic z v := latticeQuadratic_lower z v

/-- The actual nonzero-row series is convergent for each positive parameter. -/
theorem summable_latticeThetaRemainder (z : ℍ) {t : ℝ} (ht : 0 < t) :
    Summable (fun v : {v : ℤ × ℤ // v ≠ 0} => latticeThetaTerm z t v.val) :=
  (summable_latticeThetaTerm z ht).subtype {v | v ≠ 0}

/-- Removing the unique zero row gives exactly theta minus one. -/
theorem latticeThetaRemainder_eq (z : ℍ) {t : ℝ} (ht : 0 < t) :
    latticeThetaRemainder z t = latticeTheta z t - 1 := by
  classical
  have h := (summable_latticeThetaTerm z ht).tsum_eq_add_tsum_ite (0, 0)
  rw [latticeThetaTerm_zero] at h
  have he : latticeThetaRemainder z t =
      ∑' v : ℤ × ℤ, if v = (0, 0) then 0 else latticeThetaTerm z t v := by
    change (∑' v : {v : ℤ × ℤ | v ≠ 0}, latticeThetaTerm z t v.val) = _
    trans ∑' v : ℤ × ℤ, ({v : ℤ × ℤ | v ≠ 0} : Set (ℤ × ℤ)).indicator
      (latticeThetaTerm z t) v
    · exact tsum_subtype {v : ℤ × ℤ | v ≠ 0} (latticeThetaTerm z t)
    apply tsum_congr
    intro v
    simp [Set.indicator, show (0 : ℤ × ℤ) = (0, 0) from rfl]
  rw [← he] at h
  change latticeTheta z t = 1 + latticeThetaRemainder z t at h
  linarith

/-- The actual theta remainder is nonnegative. -/
theorem latticeThetaRemainder_nonneg (z : ℍ) (t : ℝ) : 0 ≤ latticeThetaRemainder z t :=
  tsum_nonneg (fun v => (latticeThetaTerm_pos z t v.val).le)

/-- A fixed summable Gaussian controls the actual nonzero summands uniformly for t≥1. -/
theorem latticeThetaTerm_decay (z : ℍ) {t : ℝ} (ht : 1 ≤ t)
    {v : ℤ × ℤ} (hv : v ≠ 0) :
    latticeThetaTerm z t v ≤ Real.exp (-(Real.pi * latticeQuadraticLower z / 2) * t) *
      latticeThetaTerm z (1 / 2) v := by
  rw [latticeThetaTerm, latticeThetaTerm, ← Real.exp_add, Real.exp_le_exp]
  have h1 := mul_nonneg (show 0 ≤ t by linarith)
    (sub_nonneg.mpr (latticeQuadratic_lower_nonzero z hv))
  have h2 := mul_nonneg (sub_nonneg.mpr ht) (latticeQuadratic_nonneg z v)
  have h3 : latticeQuadraticLower z * t / 2 + latticeQuadratic z v / 2 ≤
      t * latticeQuadratic z v := by nlinarith
  have h4 := mul_le_mul_of_nonpos_left h3 (neg_nonpos.mpr Real.pi_pos.le)
  nlinarith

/-- The literal nonzero theta tail decays exponentially with a proved positive lattice rate. -/
theorem latticeThetaRemainder_decay (z : ℍ) {t : ℝ} (ht : 1 ≤ t) :
    latticeThetaRemainder z t ≤ Real.exp (-(Real.pi * latticeQuadraticLower z / 2) * t) *
      latticeThetaRemainder z (1 / 2) := by
  rw [latticeThetaRemainder, latticeThetaRemainder, ← tsum_mul_left]
  exact (summable_latticeThetaRemainder z (by linarith : 0 < t)).tsum_le_tsum
    (fun v => latticeThetaTerm_decay z ht v.property)
    ((summable_latticeThetaRemainder z (by norm_num : (0 : ℝ) < 1 / 2)).mul_left _)

/-- Each actual Gaussian row varies continuously with the real theta parameter. -/
theorem continuous_latticeThetaTerm (z : ℍ) (v : ℤ × ℤ) :
    Continuous (fun t : ℝ => latticeThetaTerm z t v) := by
  unfold latticeThetaTerm
  fun_prop

/-- The actual theta remainder is measurable as a sum of genuine Gaussian rows. -/
theorem measurable_latticeThetaRemainder (z : ℍ) : Measurable (latticeThetaRemainder z) :=
  Measurable.tsum (fun v => (continuous_latticeThetaTerm z v.val).measurable)

end
end Dubon2026

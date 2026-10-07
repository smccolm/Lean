import Dubon2026.RectangularLatticeRows
import Dubon2026.Gamma0EisensteinUnfolding
import Dubon2026.LatticeCuspMajorant

/-! # Positive sublattice bounds for actual rescaled lattice continuations -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- A sum of genuine Eisenstein rows at a real parameter has no cancellation in its norm. -/
theorem norm_tsum_eisenstein_real {ι : Type*} (v : ι → (Fin 2 → ℤ)) (σ : ℝ) (z : ℍ) :
    ‖∑' i, nonholomorphicEisensteinTerm (σ : ℂ) (v i) z‖ =
      ∑' i, ‖nonholomorphicEisensteinTerm (σ : ℂ) (v i) z‖ := by
  simp_rw [nonholomorphicEisensteinTerm_real]
  rw [← Complex.ofReal_tsum, Complex.norm_of_nonneg
    (tsum_nonneg (fun i => Real.rpow_nonneg (eisensteinRowHeight_nonneg (v i) z) σ))]
  apply tsum_congr
  intro i
  exact (Complex.norm_of_nonneg (Real.rpow_nonneg (eisensteinRowHeight_nonneg (v i) z) σ)).symm

/-- Restricting the actual positive half-lattice sum to a rectangular sublattice only decreases its norm. -/
theorem norm_rectangularLatticeSeries_le (a b : ℕ) (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    ‖(1 / 2 : ℂ) * ∑' v : rectangularLatticeRows a b,
      nonholomorphicEisensteinTerm (σ : ℂ) v.val z‖ ≤ ‖latticeEpsteinSeries z (σ : ℂ)‖ := by
  have hsum := summable_norm_nonholomorphicEisensteinTerm (s := (σ : ℂ)) hσ z
  have hle := Summable.tsum_subtype_le
    (fun v : Fin 2 → ℤ => ‖nonholomorphicEisensteinTerm (σ : ℂ) v z‖)
    (rectangularLatticeRows a b) (fun _ => norm_nonneg _) hsum
  have he := congrArg norm (latticeEpstein_full_sum z (s := (σ : ℂ)) hσ)
  rw [norm_tsum_eisenstein_real, norm_mul, Complex.norm_ofNat] at he
  rw [norm_mul, norm_tsum_eisenstein_real]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  linarith

/-- The genuine rescaled Epstein value is controlled by the original positive lattice sum. -/
theorem norm_latticeEpsteinSeries_rectangular_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    ‖latticeEpsteinSeries (rectangularLatticePoint a b ha hb z) (σ : ℂ)‖ ≤
      ((a : ℝ) * b) ^ σ * ‖latticeEpsteinSeries z (σ : ℂ)‖ := by
  have h := norm_rectangularLatticeSeries_le a b z hσ
  rw [rectangularLatticeSeries_eq_epstein a b ha hb z (s := (σ : ℂ)) hσ, norm_mul] at h
  have hab : 0 < (a : ℝ) * b := mul_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)
  have he : (a : ℂ) * b = (((a : ℝ) * b : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hab, Complex.neg_re, Complex.ofReal_re,
    Real.rpow_neg hab.le, inv_mul_eq_div, div_le_iff₀ (Real.rpow_pos_of_pos hab σ)] at h
  simpa only [mul_comm] using h

/-- The actual rescaled completed value has the same exact positive sublattice majorant factor. -/
theorem norm_latticeCompletedMellin_rectangular_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    ‖latticeCompletedMellin (rectangularLatticePoint a b ha hb z) (σ : ℂ)‖ ≤
      ((a : ℝ) * b) ^ σ * ‖latticeCompletedMellin z (σ : ℂ)‖ := by
  rw [latticeCompletedMellin_eq_epstein _ (s := (σ : ℂ)) hσ,
    latticeCompletedMellin_eq_epstein _ (s := (σ : ℂ)) hσ, norm_mul, norm_mul]
  have h := mul_le_mul_of_nonneg_left (norm_latticeEpsteinSeries_rectangular_le a b ha hb z hσ)
    (norm_nonneg ((Real.pi : ℂ) ^ (-(σ : ℂ)) * Complex.Gamma (σ : ℂ)))
  simpa only [norm_mul, mul_left_comm, mul_assoc] using h

/-- The actual rational positive rescaling is continuous in the upper-half-plane variable. -/
theorem continuous_rectangularLatticePoint (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (rectangularLatticePoint a b ha hb) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply (isEmbedding_coe.continuousAt_iff).mpr
  simpa only [Function.comp_def, coe_rectangularLatticePoint] using
    (continuousAt_const.mul continuous_coe.continuousAt :
      ContinuousAt (fun w : ℍ => ((a : ℂ) / b) * (w : ℂ)) z)

/-- Each rescaled positive lattice value remains integrable against the actual cusp density on Gamma0(Q). -/
theorem integrableOn_norm_rectangular_lattice_petersson {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun z : ℍ =>
      ‖latticeCompletedMellin (rectangularLatticePoint a b ha hb z) (σ : ℂ)‖ * ‖petersson k f f z‖)
      (gamma0FundamentalDomain Q) := by
  have hm := ((measurable_latticeCompletedMellin (σ : ℂ)).comp
    (continuous_rectangularLatticePoint a b ha hb).measurable).norm.mul
      (petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous f)).norm.measurable
  apply ((integrableOn_norm_lattice_petersson_gamma0 f (s := (σ : ℂ)) hσ).const_mul
    (((a : ℝ) * b) ^ σ)).mono' hm.aestronglyMeasurable.restrict
  apply ae_of_all
  intro z
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_latticeCompletedMellin_rectangular_le a b ha hb z hσ)
    (norm_nonneg _)

end
end Dubon2026

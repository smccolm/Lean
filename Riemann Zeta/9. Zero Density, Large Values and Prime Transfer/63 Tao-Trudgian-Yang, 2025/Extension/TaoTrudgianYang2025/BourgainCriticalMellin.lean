import TaoTrudgianYang2025.ZetaMellinShift
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import GuthMaynard.DFIEquation29

/-!
# Scale-faithful Mellin entry for Bourgain's critical weights

A fixed positive compact profile is dilated and multiplied by the genuine
critical weight x^(-1/2). Its Mellin kernel on the critical line has no
physical-scale loss. The moving pole retains its square-root scale factor.
These are the exact analytic identities needed before finite localization.
-/

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- A real power times an actual compact positive-half-line profile. -/
def bourgainRealPowerWeight (a : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x ^ a : ℝ) * g x

/-- A real power does not spoil smoothness: the profile vanishes on a
neighborhood of the only singular point. -/
def bourgainRealPowerWeightTest {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (a : ℝ) :
    DFIVoronoiTestFunction (bourgainRealPowerWeight a g) := by
  refine ⟨hg.lower, hg.upper, hg.lower_pos, hg.lower_le_upper, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      have heq : bourgainRealPowerWeight a g =ᶠ[nhds (0 : ℝ)] 0 := by
        filter_upwards [Iio_mem_nhds hg.lower_pos] with y hy
        have hgy : g y = 0 := by
          by_contra hn
          exact (not_le_of_gt hy) (hg.support_subset hn).1
        simp [bourgainRealPowerWeight, hgy]
      exact contDiffAt_const.congr_of_eventuallyEq heq
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (Real.contDiffAt_rpow_const_of_ne hx)).mul hg.smooth.contDiffAt
  · intro x hx
    apply hg.support_subset
    intro hzero
    exact hx (by simp [bourgainRealPowerWeight, hzero])

/-- Exact Mellin-coordinate shift for the genuine real-power weight. -/
theorem mellin_bourgainRealPowerWeight (a : ℝ) (g : ℝ → ℂ) (s : ℂ) :
    mellin (bourgainRealPowerWeight a g) s = mellin g (s + (a : ℂ)) := by
  calc
    _ = mellin (fun x : ℝ => (x : ℂ) ^ (a : ℂ) * g x) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [bourgainRealPowerWeight, Complex.ofReal_cpow hx.le]
    _ = _ := by simpa only [smul_eq_mul] using mellin_cpow_smul g s (a : ℂ)

/-- The actual dilated profile is again a native smooth positive test. -/
def bourgainDilatedProfileTest {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {L : ℝ} (hL : 0 < L) :
    DFIVoronoiTestFunction (fun x => g (x / L)) := by
  simpa only [div_eq_mul_inv, mul_comm] using
    hg.scaleNormalize (L⁻¹) (inv_pos.mpr hL)

/-- Mellin dilation, with the physical-scale factor explicit. -/
theorem mellin_bourgainDilatedProfile (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (s : ℂ) :
    mellin (fun x => g (x / L)) s = (L : ℂ) ^ s * mellin g s := by
  have h := mellin_eq_scale_cpow_mul_normalized (fun x => g (x / L)) L hL s
  simpa only [mul_div_cancel_left₀ _ hL.ne'] using h

/-- The critical coefficient weight used in the smoothed majorant. -/
def bourgainCriticalWeight (g : ℝ → ℂ) (L x : ℝ) : ℂ :=
  bourgainRealPowerWeight (-1/2) (fun y => g (y / L)) x

/-- All smoothness and support requirements are supplied by the fixed profile. -/
def bourgainCriticalWeightTest {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {L : ℝ} (hL : 0 < L) :
    DFIVoronoiTestFunction (bourgainCriticalWeight g L) :=
  bourgainRealPowerWeightTest (bourgainDilatedProfileTest hg hL) (-1/2)

/-- Exact transform of the dilated critical coefficient weight. -/
theorem mellin_bourgainCriticalWeight (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (s : ℂ) :
    mellin (bourgainCriticalWeight g L) s =
      (L : ℂ) ^ (s - 1/2) * mellin g (s - 1/2) := by
  unfold bourgainCriticalWeight
  rw [mellin_bourgainRealPowerWeight, mellin_bourgainDilatedProfile g hL]
  congr 2 <;> push_cast <;> ring

/-- The critical-line Mellin kernel is independent of the scale in norm. -/
theorem norm_bourgainCriticalWeight_mellin_critical
    (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (u : ℝ) :
    ‖mellin (bourgainCriticalWeight g L) ((1/2 : ℂ) + (u : ℂ)*I)‖ =
      ‖mellin g ((u : ℂ)*I)‖ := by
  rw [mellin_bourgainCriticalWeight g hL]
  have heq : (1/2 : ℂ) + (u : ℂ)*I - 1/2 = (u : ℂ)*I := by ring
  rw [heq, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hL]
  simp

/-- The moving pole has precisely the square-root scale normalization. -/
theorem norm_bourgainCriticalWeight_mellin_residue
    (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    ‖mellin (bourgainCriticalWeight g L) (1 - (t : ℂ)*I)‖ =
      Real.sqrt L * ‖mellin g ((1/2 : ℂ) - (t : ℂ)*I)‖ := by
  rw [mellin_bourgainCriticalWeight g hL]
  have heq : (1 : ℂ) - (t : ℂ)*I - 1/2 = (1/2 : ℂ) - (t : ℂ)*I := by ring
  rw [heq, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hL]
  have hre : ((1/2 : ℂ) - (t : ℂ)*I).re = (1/2 : ℝ) := by simp
  rw [hre, Real.sqrt_eq_rpow]

/-- Arbitrary-order decay is uniform in the physical dilation. -/
theorem bourgainCriticalWeight_mellin_bounds {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ u : ℝ,
      (1+|u|)^q * ‖mellin (bourgainCriticalWeight g L) ((1/2 : ℂ)+(u : ℂ)*I)‖ ≤ C ∧
      (1+|u|)^q * ‖mellin (bourgainCriticalWeight g L) (1-(u : ℂ)*I)‖ ≤
        C * Real.sqrt L := by
  obtain ⟨C₀, hC₀, hzero⟩ := hg.exists_mellin_one_add_abs_pow_line_bound q 0
  obtain ⟨C₁, hC₁, hhalf⟩ := hg.exists_mellin_one_add_abs_pow_line_bound q (1/2)
  refine ⟨C₀+C₁+1, by positivity, ?_⟩
  intro L hL u
  constructor
  · rw [norm_bourgainCriticalWeight_mellin_critical g hL]
    have h := hzero u
    norm_num only [ofReal_zero, zero_add] at h
    linarith
  · rw [norm_bourgainCriticalWeight_mellin_residue g hL]
    have h := hhalf (-u)
    simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg, abs_neg,
      ofReal_div, ofReal_one, ofReal_ofNat] at h
    have hs := mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg L)
    nlinarith [Real.sqrt_nonneg L]

/-- Exact zeta representation of the actual critical weighted polynomial,
including the moving-pole residue. No contour or integrability input is assumed. -/
theorem bourgainCriticalWeight_zeta_mellin_entry {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (∑' n : ℕ, bourgainCriticalWeight g L n * dirichletPhase n t) =
      (L : ℂ) ^ ((1/2 : ℂ)-(t : ℂ)*I) *
        mellin g ((1/2 : ℂ)-(t : ℂ)*I) +
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        riemannZeta ((1/2 : ℂ) + ((u+t : ℝ) : ℂ)*I) *
          ((L : ℂ)^((u : ℂ)*I) * mellin g ((u : ℂ)*I)) := by
  have h := smooth_dirichlet_sum_eq_critical_zeta_mellin
    (bourgainCriticalWeightTest hg hL) t
  simp_rw [mellin_bourgainCriticalWeight g hL] at h
  have hres : (1 : ℂ)-(t : ℂ)*I-1/2 = (1/2 : ℂ)-(t : ℂ)*I := by ring
  have hcrit (u : ℝ) : (1/2 : ℂ)+(u : ℂ)*I-1/2 = (u : ℂ)*I := by ring
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  simp only [hres, hcrit] at h
  exact h

end TaoTrudgianYang2025

import TaoTrudgianYang2025.AtkinsonRootAmplitudeDerivatives
import GuthMaynard.DFIParametricMellin

/-!
# The actual positive-root Fourier amplitude

Extension by zero removes the negative square-root branch. The physical
band itself supplies a neighbourhood of zero on which the extension vanishes.
No auxiliary cutoff is inserted into the source.
-/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped ContDiff FourierTransform Topology

namespace TaoTrudgianYang2025

def atkinsonRootFourierAmplitude (T G L α u : ℝ) : ℂ :=
  if 0 < u then atkinsonRootFourierCore T G L α u else 0

theorem support_zetaDivisorBandCutoff_physical {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Function.support (zetaDivisorBandCutoff T G L) ⊆ Icc (T / 16) T := by
  intro x hx
  have hs := support_zetaDivisorBandCutoff hT hG hL hx
  have hb := zetaDivisorBandEdge_outer_bounds hT hG hL.le hwidth
  have hlow : T / 16 ≤ T / (4 * Real.pi) :=
    div_le_div_of_nonneg_left hT.le (by positivity) (by nlinarith [Real.pi_lt_four])
  have hhigh : T / Real.pi ≤ T := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  exact ⟨hlow.trans (hb.1.trans hs.1), (hs.2.trans hb.2).trans hhigh⟩

theorem support_atkinsonRootFourierAmplitude {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α : ℝ) :
    Function.support (atkinsonRootFourierAmplitude T G L α) ⊆ Icc (1 / 4) 1 := by
  intro u hu
  have hu0 : 0 < u := by
    by_contra hn
    exact hu (by simp [atkinsonRootFourierAmplitude, hn])
  have hc : zetaDivisorBandCutoff T G L (T * u ^ 2) ≠ 0 := by
    intro hz
    exact hu (by simp [atkinsonRootFourierAmplitude, hu0, atkinsonRootFourierCore, hz])
  have hs := support_zetaDivisorBandCutoff_physical hT hG hL hwidth hc
  have hlo : 1 / 16 ≤ u ^ 2 := by nlinarith [hs.1]
  have hhi : u ^ 2 ≤ 1 := by nlinarith [hs.2]
  constructor <;> nlinarith

theorem atkinsonRootFourierAmplitude_eventuallyEq_core (T G L α : ℝ)
    {u : ℝ} (hu : 0 < u) :
    atkinsonRootFourierAmplitude T G L α =ᶠ[𝓝 u] atkinsonRootFourierCore T G L α := by
  filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
  simp only [atkinsonRootFourierAmplitude, if_pos (show 0 < v from hv)]

theorem contDiffAt_atkinsonRootFourierCore {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (L α : ℝ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ (atkinsonRootFourierCore T G L α) u := by
  have hw := contDiff_zetaDivisorWeight
  have hc := contDiff_zetaDivisorBandCutoff T G L
  have hg := contDiff_zetaGaussianQuadraticIntegral T hG
  have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  unfold atkinsonRootFourierCore atkinsonPowerProfile zetaMainMellinProfile
    atkinsonPhaseExponential atkinsonRootStationaryProfile
  fun_prop (disch := positivity)

theorem contDiff_atkinsonRootFourierAmplitude {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α : ℝ) :
    ContDiff ℝ ∞ (atkinsonRootFourierAmplitude T G L α) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0 < u
  · exact (contDiffAt_atkinsonRootFourierCore hT hG.ne' L α hu).congr_of_eventuallyEq
      (atkinsonRootFourierAmplitude_eventuallyEq_core T G L α hu)
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds (show u < (1 / 4 : ℝ) by linarith)] with v hv
    by_contra hn
    have hs := support_atkinsonRootFourierAmplitude hT hG hL hwidth α hn
    exact (not_lt_of_ge hs.1) hv

theorem hasCompactSupport_atkinsonRootFourierAmplitude {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α : ℝ) :
    HasCompactSupport (atkinsonRootFourierAmplitude T G L α) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro u hu
  by_contra hn
  exact hu (support_atkinsonRootFourierAmplitude hT hG hL hwidth α hn)

theorem exists_intervalC2Bound_atkinsonRootFourierAmplitude (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      IntervalC2Bound (atkinsonRootFourierAmplitude T G L α)
        (1 / 4) 1 (C * G * T ^ (-α)) T := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonRootFourierCore α
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  apply (hbound T G L hT hG hGT hL hwidth).congr_of_eventuallyEq
  intro u hu
  exact (atkinsonRootFourierAmplitude_eventuallyEq_core T G L α
    (show 0 < u by linarith [hu.1])).symm

end TaoTrudgianYang2025

import PrimeShell.AmplitudeNoGain

namespace PrimeShell

noncomputable section

open Filter Function MeasureTheory Set intervalIntegral
open Zeta23 Zeta23.XiPrime

/-- The right-band center is an interior point at which the concrete
amplitude profile has positive mass. -/
theorem twoBandAmplitude_mass_pos :
    0 < ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      amplitudeSq twoBandAmplitude s := by
  let v := amplitudeSq twoBandAmplitude
  have hvcont : Continuous v :=
    twoBandAmplitude_profile.contDiff.continuous.pow 2
  have hvint : IntervalIntegrable v volume (-(1 : ℝ) / 2) (1 / 2) :=
    hvcont.intervalIntegrable _ _
  have hvnonneg : 0 ≤ᵐ[volume] v :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    hvnonneg hvint]
  constructor
  · norm_num
  · let U := support v ∩ Ioo (-(1 : ℝ) / 2) (1 / 2)
    have hUopen : IsOpen U := hvcont.isOpen_support.inter isOpen_Ioo
    have hcenterV : v shellBandCenter ≠ 0 := by
      unfold v amplitudeSq
      exact pow_ne_zero 2 twoBandAmplitude_center_pos.ne'
    have hcenterInterior :
        shellBandCenter ∈ Ioo (-(1 : ℝ) / 2) (1 / 2) := by
      norm_num [shellBandCenter]
    have hUnonempty : U.Nonempty :=
      ⟨shellBandCenter, mem_inter (mem_support.mpr hcenterV) hcenterInterior⟩
    have hUpos : 0 < volume U := hUopen.measure_pos volume hUnonempty
    have hsubset : U ⊆ support v ∩ Ioc (-(1 : ℝ) / 2) (1 / 2) := by
      intro x hx
      exact ⟨hx.1, Ioo_subset_Ioc_self hx.2⟩
    exact hUpos.trans_le (measure_mono hsubset)

theorem twoBandAmplitude_support_split :
    ∀ s ∈ Icc (-(1 : ℝ) / 2) (1 / 2), twoBandAmplitude s ≠ 0 →
      s ≤ -(499 / 1000 : ℝ) ∨ (499 / 1000 : ℝ) ≤ s := by
  intro s _ hs
  rcases inTwoBand_of_twoBandAmplitude_ne_zero hs with hright | hleft
  · right
    rw [abs_lt] at hright
    unfold shellBandCenter shellBandOuterRadius at hright
    linarith
  · left
    rw [abs_lt] at hleft
    unfold shellBandCenter shellBandOuterRadius at hleft
    linarith

/-- The corrected amplitude interface is genuinely inhabited by the
literal two-band bump.  This rules out vacuity in the universal no-gain
theorem. -/
def concreteFaithfulAmplitudeShell : FaithfulAmplitudeShell where
  A := concretePrimeShellFullChainAdmissible
  q := twoBandAmplitude
  amplitude := twoBandAmplitude_profile
  leftEdge := -(499 / 1000 : ℝ)
  rightEdge := 499 / 1000
  left_mem := by norm_num
  right_mem := by norm_num
  edge_order := by norm_num
  symmetric_edges := by norm_num
  support_split := twoBandAmplitude_support_split
  left_present := by
    refine ⟨-shellBandCenter, ?_, ?_⟩
    · constructor <;> norm_num [shellBandCenter]
    · rw [twoBandAmplitude_even]
      exact twoBandAmplitude_center_pos.ne'
  right_present := by
    refine ⟨shellBandCenter, ?_, twoBandAmplitude_center_pos.ne'⟩
    constructor <;> norm_num [shellBandCenter]
  left_low_block := by
    norm_num [concretePrimeShellFullChainAdmissible,
      concretePrimeShellAdmissible, concretePrimeShellParams]
  right_low_block := by
    norm_num [concretePrimeShellFullChainAdmissible,
      concretePrimeShellAdmissible, concretePrimeShellParams]
  cross_beyond_support_one := by
    norm_num [concretePrimeShellFullChainAdmissible,
      concretePrimeShellAdmissible, concretePrimeShellParams]
  mass_pos := twoBandAmplitude_mass_pos

theorem faithfulAmplitudeShell_nonempty : Nonempty FaithfulAmplitudeShell :=
  ⟨concreteFaithfulAmplitudeShell⟩

theorem concreteFaithfulAmplitudeShell_kappaXi_gt_three :
    3 < kappaXi
      concretePrimeShellParams.lam (amplitudeSq twoBandAmplitude) := by
  simpa [concreteFaithfulAmplitudeShell, concretePrimeShellFullChainAdmissible,
    concretePrimeShellAdmissible] using
    concreteFaithfulAmplitudeShell.kappaXi_gt_three

theorem concreteFaithfulAmplitudeShell_no_positive_gain
    {delta : ℝ} (hdelta : 0 < delta) :
    ¬ ((2 / 3 : ℝ) + delta <
      2 - kappaXi concretePrimeShellParams.lam
        (amplitudeSq twoBandAmplitude)) := by
  simpa [concreteFaithfulAmplitudeShell, concretePrimeShellFullChainAdmissible,
    concretePrimeShellAdmissible] using
    concreteFaithfulAmplitudeShell.no_positive_gain hdelta

end

end PrimeShell

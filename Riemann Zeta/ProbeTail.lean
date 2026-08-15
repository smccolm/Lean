import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_tail
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ‖dfiEquation29InitialTransform q branch g n‖ ≤
      ‖dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)‖ ^ k *
        ((14 * Real.pi + 8) / Real.sqrt q *
          (dfiBesselQuarterBaseNorm
            (dfiEquation29BesselRecurrenceIterate k g) *
              (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  let G : ℝ → ℂ := dfiEquation29BesselRecurrenceIterate k g
  have hG : DFIVoronoiTestFunction G := hg.besselRecurrenceIterate k
  have heq : dfiEquation29InitialTransform q branch g n =
      (dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) ^ k *
        dfiEquation29InitialTransform q branch G n := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n
          (-(1 / 2 : ℝ) - k) :=
        hg.dfiEquation29TransformAt_shift q k branch hn
      _ = (dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) ^ k *
          dfiEquation29TransformAt q branch G n (-(1 / 2 : ℝ)) := by
        simpa [G] using
          hg.dfiEquation29TransformAt_sub_nat_besselRecurrence
            q branch hn k (-(1 / 2 : ℝ)) (by norm_num)
      _ = _ := by rw [dfiEquation29TransformAt_initial]
  have hPhysical :=
    hG.norm_dfiEquation29InitialTransform_le_besselQuarterNorm
      q branch hn (hG.integrableOn_besselQuarterWeight_mul_nat n hn)
  rw [dfiBesselQuarterNorm_eq_rpow_mul_base G n hn] at hPhysical
  rw [heq, norm_mul, norm_pow]
  gcongr
  simpa [G, mul_comm] using hPhysical

theorem probe_tail_quantitative
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S))
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (k : ℕ)
    (hD : (2 * k + 3 : ℕ) ≤ D)
    (hDeriv : ∀ r ≤ 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤ A * B ^ r) :
    ‖dfiEquation29InitialTransform q branch g n‖ ≤
      (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        ((14 * Real.pi + 8) / Real.sqrt q *
          ((S ^ (-(1 / 4 : ℝ)) *
            (S * (A * (D * S * B ^ 2) ^ k))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  have hRec := hg.norm_dfiEquation29InitialTransform_le_recurrence
    q branch hn k
  rw [norm_dfiEquation29BranchShiftMultiplier q branch n] at hRec
  have hBase := hg.dfiBesselQuarterBaseNorm_besselRecurrenceIterate_le
    hA hB hS hSB hSupport k hD hDeriv
  exact hRec.trans (by gcongr)

end RiemannZeta.GuthMaynard

import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_norm
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S)) (k : ℕ)
    (hD : (2 * k + 3 : ℕ) ≤ D)
    (hDeriv : ∀ r ≤ 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤ A * B ^ r) :
    dfiBesselQuarterBaseNorm
        (dfiEquation29BesselRecurrenceIterate k g) ≤
      S ^ (-(1 / 4 : ℝ)) *
        (S * (A * (D * S * B ^ 2) ^ k)) := by
  let G : ℝ → ℂ := dfiEquation29BesselRecurrenceIterate k g
  let K : ℝ := A * (D * S * B ^ 2) ^ k
  have hG : DFIVoronoiTestFunction G := hg.besselRecurrenceIterate k
  have hGSupport : Function.support G ⊆ Set.Icc S (2 * S) := by
    simpa [G] using hg.support_besselRecurrenceIterate_subset hSupport k
  have hPoint : ∀ x ∈ Set.Icc S (2 * S), ‖G x‖ ≤ K := by
    intro x hx
    have hout := hg.norm_iteratedDeriv_besselRecurrenceIterate_le
      hA hB hS hSB hSupport k 0 (by simpa using hD) (by simpa using hDeriv)
      0 (by simp) x hx
    simpa [G, K] using hout
  have hLeft : IntegrableOn (fun x : ℝ => ‖G x‖) (Set.Icc S (2 * S)) :=
    hG.continuous.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hRight : IntegrableOn (fun _ : ℝ => K) (Set.Icc S (2 * S)) :=
    integrableOn_const (ne_of_lt isCompact_Icc.measure_lt_top)
  have hIntegral : (∫ x in Set.Icc S (2 * S), ‖G x‖) ≤ S * K := by
    calc
      (∫ x in Set.Icc S (2 * S), ‖G x‖) ≤
          ∫ _x in Set.Icc S (2 * S), K := by
        apply integral_mono_ae hLeft hRight
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact hPoint x hx
      _ = (2 * S - S) * K := by
        rw [setIntegral_const, Real.volume_real_Icc]
        simp only [smul_eq_mul]
        rw [max_eq_left (by linarith)]
      _ = S * K := by ring
  calc
    dfiBesselQuarterBaseNorm G ≤
        S ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc S (2 * S), ‖G x‖) :=
      dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
        hS hG hGSupport
    _ ≤ S ^ (-(1 / 4 : ℝ)) * (S * K) := by
      exact mul_le_mul_of_nonneg_left hIntegral (Real.rpow_nonneg hS.le _)
    _ = S ^ (-(1 / 4 : ℝ)) *
        (S * (A * (D * S * B ^ 2) ^ k)) := rfl

end RiemannZeta.GuthMaynard

import GafniTao.FordVKTrigonometricContradiction
import GafniTao.FordSource

/-!
# The asymptotic Vinogradov--Korobov zero-free region
-/

namespace GafniTao

noncomputable section

private abbrev fordVKProofA : ℝ := fordQualitativeGlobalCoefficient
private abbrev fordVKProofB : ℝ := fordSourceB 3000000

noncomputable def fordVKDominationCoefficient : ℝ :=
  fordTrigB1 fordVKA1 fordVKA2 *
      (fordVKMajorantCoefficient fordVKProofA fordVKProofB + 2) +
    4 * fordVKAuxiliaryTrigCoefficient *
      (fordVKMajorantCoefficient fordVKProofA fordVKProofB + 1)

noncomputable def fordVKZeroFreeConstant : ℝ :=
  min (1 / 2) (fordVKTrigGap / (2 * fordVKDominationCoefficient))

private theorem fordVKProofA_one_le : 1 ≤ fordVKProofA := by
  change 1 ≤ fordQualitativeGlobalCoefficient
  unfold fordQualitativeGlobalCoefficient
  linarith [fordQualitativeZetaCoefficient_nonneg]

private theorem fordVKProofB_nonneg : 0 ≤ fordVKProofB :=
  fordSourceB_three_million_pos.le

theorem fordVKDominationCoefficient_pos :
    0 < fordVKDominationCoefficient := by
  have hC := fordVKMajorantCoefficient_pos
    fordVKProofA_one_le fordVKProofB_nonneg
  have hb1 : 0 < fordTrigB1 fordVKA1 fordVKA2 := by
    norm_num [fordVKA1, fordVKA2, fordTrigB1]
  obtain ⟨_hb0, _hb1, hb2, hb3, hb4⟩ := fordVK_trig_coefficients_nonneg
  have haux : 0 ≤ fordVKAuxiliaryTrigCoefficient := by
    unfold fordVKAuxiliaryTrigCoefficient
    linarith
  unfold fordVKDominationCoefficient
  positivity

theorem fordVKZeroFreeConstant_pos : 0 < fordVKZeroFreeConstant := by
  unfold fordVKZeroFreeConstant
  exact lt_min (by norm_num) (div_pos fordVKTrigGap_pos
    (mul_pos two_pos fordVKDominationCoefficient_pos))

theorem fordVKZeroFreeConstant_le_half :
    fordVKZeroFreeConstant ≤ 1 / 2 := by
  exact min_le_left _ _

theorem fordVKZeroFreeConstant_domination :
    fordTrigB1 fordVKA1 fordVKA2 *
          (fordVKMajorantCoefficient fordVKProofA fordVKProofB + 1 +
            (1 / 27 : ℝ) * fordVKZeroFreeConstant) +
        4 * fordVKAuxiliaryTrigCoefficient *
          (fordVKMajorantCoefficient fordVKProofA fordVKProofB + 1) <
      fordVKTrigGap / fordVKZeroFreeConstant := by
  let c := fordVKZeroFreeConstant
  let K := fordVKDominationCoefficient
  have hc : 0 < c := fordVKZeroFreeConstant_pos
  have hcHalf : c ≤ 1 / 2 := fordVKZeroFreeConstant_le_half
  have hK : 0 < K := fordVKDominationCoefficient_pos
  have hcK : c ≤ fordVKTrigGap / (2 * K) := by
    exact min_le_right _ _
  have hmul : c * (2 * K) ≤ fordVKTrigGap :=
    (le_div_iff₀ (mul_pos two_pos hK)).mp hcK
  have hKlt : K < fordVKTrigGap / c := by
    apply (lt_div_iff₀ hc).mpr
    nlinarith [fordVKTrigGap_pos]
  have hb1 : 0 ≤ fordTrigB1 fordVKA1 fordVKA2 :=
    fordVK_trig_coefficients_nonneg.2.1
  have hinner :
      fordVKMajorantCoefficient fordVKProofA fordVKProofB + 1 +
          (1 / 27 : ℝ) * c ≤
        fordVKMajorantCoefficient fordVKProofA fordVKProofB + 2 := by
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hinner hb1
  change _ < fordVKTrigGap / c
  apply lt_of_le_of_lt _ hKlt
  dsimp [K]
  unfold fordVKDominationCoefficient
  simpa [c] using add_le_add_right hfirst
    (4 * fordVKAuxiliaryTrigCoefficient *
      (fordVKMajorantCoefficient fordVKProofA fordVKProofB + 1))

private theorem eventually_fordVKScaleData :
    ∀ᶠ t : ℝ in Filter.atTop, FordVKScaleData t := by
  have hsource : ∀ᶠ t : ℝ in Filter.atTop,
      Real.exp (Real.exp 1) ≤ t ∧
      9 ≤ fordVKLogLog t ∧
      2 * Real.log (fordVKLogLog t) ≤ fordVKLogLog t ∧
      fordVKRadius t ≤ 1 / 8 := eventually_fordVK_scale_data
  filter_upwards [hsource] with t ht
  exact ⟨ht.1, ht.2.1, ht.2.2.2⟩

private theorem fordVK_positive_height_zero_free :
    ∃ H : ℝ, Real.exp (Real.exp 1) ≤ H ∧
      ∀ ⦃rho : ℂ⦄, riemannZeta rho = 0 → H ≤ rho.im →
        rho.re < 1 - fordVKZeroFreeConstant /
          vinogradovKorobovDenominator rho.im := by
  obtain ⟨Hscale, hHscale⟩ := Filter.eventually_atTop.mp
    eventually_fordVKScaleData
  let H : ℝ := max 100 (max (Real.exp (Real.exp 1)) Hscale)
  refine ⟨H, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · intro rho hrhoZero hheight
    have ht : 100 ≤ rho.im := (le_max_left _ _).trans hheight
    have hscale : FordVKScaleData rho.im :=
      hHscale _ ((le_max_right _ _).trans (le_max_right _ _) |>.trans hheight)
    have hscale2 : FordVKScaleData (2 * rho.im) :=
      hHscale _ (le_trans ((le_max_right _ _).trans (le_max_right _ _))
        (by nlinarith))
    have hscale3 : FordVKScaleData (3 * rho.im) :=
      hHscale _ (le_trans ((le_max_right _ _).trans (le_max_right _ _))
        (by nlinarith))
    have hscale4 : FordVKScaleData (4 * rho.im) :=
      hHscale _ (le_trans ((le_max_right _ _).trans (le_max_right _ _))
        (by nlinarith))
    by_contra hstrip
    exact fordVK_no_positive_height_zero ford_qualitative_general_zeta_growth
      fordVKProofA_one_le fordVKProofB_nonneg fordVKZeroFreeConstant_pos
      fordVKZeroFreeConstant_le_half fordVKZeroFreeConstant_domination ht
      hscale hscale2 hscale3 hscale4 hrhoZero rfl (le_of_not_gt hstrip)

/-- Ford's asymptotic Vinogradov--Korobov zero-free region, derived from the
proved global zeta-growth bound and the five-frequency detector. -/
theorem ford_asymptotic_zero_free_native : FordAsymptoticZeroFree := by
  obtain ⟨H, hHbase, hpositive⟩ := fordVK_positive_height_zero_free
  refine ⟨fordVKZeroFreeConstant, H, fordVKZeroFreeConstant_pos,
    hHbase, ?_⟩
  intro rho hrhoZero hheight
  by_cases him : 0 ≤ rho.im
  · simpa [abs_of_nonneg him] using
      hpositive hrhoZero (by simpa [abs_of_nonneg him] using hheight)
  · have himNonpos : rho.im ≤ 0 := le_of_not_ge him
    have hrhoNe : rho ≠ 1 := by
      intro hrho
      subst rho
      simp at hheight
      have hHpos : 0 < H := (Real.exp_pos _).trans_le hHbase
      linarith
    have hconjZero : riemannZeta (star rho) = 0 := by
      rw [RiemannZeta.GuthMaynard.riemannZeta_conj rho hrhoNe, hrhoZero]
      simp
    have hconjHeight : H ≤ (star rho).im := by
      simpa [abs_of_nonpos himNonpos] using hheight
    have h := hpositive hconjZero hconjHeight
    simpa [abs_of_nonpos himNonpos] using h

#print axioms fordVKZeroFreeConstant_pos
#print axioms fordVKZeroFreeConstant_domination
#print axioms ford_asymptotic_zero_free_native

end

end GafniTao

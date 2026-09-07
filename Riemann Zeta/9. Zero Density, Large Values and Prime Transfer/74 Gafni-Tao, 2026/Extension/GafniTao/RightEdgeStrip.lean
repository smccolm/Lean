import GafniTao.RefinedEnvelope
import GafniTao.RightEdgePhysical

/-!
# Right-edge half-open strip consumer

The right-edge argument is cancellation-free at the weighted-mass level.
This file uses that form to control each literal equation-(2.7) strip lying
inside the fixed Vinogradov--Korobov band.
-/

open Complex Finset Set
open Asymptotics Filter
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- A half-open strip contained in the right-edge rectangle is bounded by
the complete multiplicity-weighted absolute right-edge mass. -/
theorem norm_halfOpenZeroStripIncrementSum_le_rightEdgeWeight
    {eta sigmaLower sigmaUpper T tau X x : ℝ}
    (hsigmaLower : 1 - eta ≤ sigmaLower)
    (htau : 0 < tau) (hX : 1 ≤ X)
    (hxLower : X ≤ x) (hxUpper : x ≤ 2 * X) :
    ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ≤
      (2 * X / tau) * rightEdgeZeroWeight eta T X := by
  classical
  let S := halfOpenZeroStrip sigmaLower sigmaUpper T
  let R := RiemannZeta.GuthMaynard.zerosInRect (1 - eta) 1 (-T) T
  have hSubset : S ⊆ R := by
    intro rho hrho
    have hrhoData := Finset.mem_filter.mp hrho
    have hzero := mem_zeroSet_zero_data hrhoData.1
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta) 1 (-T) T
    rw [RiemannZeta.GuthMaynard.zerosInRect, Set.Finite.mem_toFinset,
      Set.mem_inter_iff, RiemannZeta.GuthMaynard.mem_ZeroRectangle]
    exact ⟨⟨hsigmaLower.trans hrhoData.2.1, hzero.2.1,
      hzero.2.2.1, hzero.2.2.2.1⟩, hzero.2.2.2.2⟩
  have hPoint : ∀ rho ∈ S,
      ‖(zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho‖ ≤
        (zeroMultiplicity rho : ℝ) *
          ((2 * X / tau) * X ^ (rho.re - 1)) := by
    intro rho hrho
    have hrhoData := Finset.mem_filter.mp hrho
    have hzero := mem_zeroSet_zero_data hrhoData.1
    have hrePos := zero_re_pos_of_nonneg hzero.1 hzero.2.1 hzero.2.2.2.2
    have hrhoNe : rho ≠ 0 := by
      intro h
      subst rho
      norm_num at hrePos
    have hxPos : 0 < x := zero_lt_one.trans_le (hX.trans hxLower)
    rw [norm_mul, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      ‖zeroIncrementTerm tau x rho‖ ≤ x ^ rho.re / tau :=
        norm_zeroIncrementTerm_le htau hxPos hrhoNe hzero.2.1
      _ ≤ (2 * X * X ^ (rho.re - 1)) / tau := by
        exact div_le_div_of_nonneg_right
          (rpow_le_two_mul_rightEdgeWeight hX hxLower hxUpper
            hzero.1 hzero.2.1) htau.le
      _ = (2 * X / tau) * X ^ (rho.re - 1) := by ring
  rw [halfOpenZeroStripIncrementSum]
  change ‖∑ rho ∈ S,
      (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho‖ ≤ _
  calc
    ‖∑ rho ∈ S,
        (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho‖ ≤
      ∑ rho ∈ S,
        ‖(zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ S, (zeroMultiplicity rho : ℝ) *
          ((2 * X / tau) * X ^ (rho.re - 1)) :=
      Finset.sum_le_sum hPoint
    _ = (2 * X / tau) *
        ∑ rho ∈ S, (zeroMultiplicity rho : ℝ) * X ^ (rho.re - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho _hrho
      ring
    _ ≤ (2 * X / tau) *
        ∑ rho ∈ R, (zeroMultiplicity rho : ℝ) * X ^ (rho.re - 1) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum_of_subset_of_nonneg hSubset fun rho _ _ =>
          mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
      · positivity
    _ = (2 * X / tau) * rightEdgeZeroWeight eta T X := by
      rfl

/-- The literal equation-(2.7) event for any strip inside the fixed
right-edge band is eventually empty. -/
theorem eventually_equation27StripLargeSet_eq_empty_of_rightEdge
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {J j : ℕ} (hJ : 0 < J)
    {theta delta : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hAtRight : 1 - nearOneRightEdgeWidth C 2 ≤ (j : ℝ) / J) :
    ∀ᶠ X : ℝ in Filter.atTop,
      equation27StripLargeSet J j theta delta X = ∅ := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJOne : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hMass :=
    eventually_two_mul_rightEdgeZeroWeight_le_physical_stretched_exp
      hDensity hZeroFree hC hc hJr hthetaLower hthetaUpper
  have hScaleLarge := tendsto_vinogradovKorobovDecayScale_atTop.eventually
    (Filter.eventually_gt_atTop
      (-Real.log (delta / (3 * J)) / (c / 16)))
  filter_upwards [hMass, hScaleLarge,
      Filter.eventually_ge_atTop (1 : ℝ)] with X hMassX hScaleX hX
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have htau : 0 < localTau X theta := localTau_pos hXPos
  have hdeltaScale : 0 < delta / (3 * (J : ℝ)) := by positivity
  have hDecaySmall :
      Real.exp (-(c / 16) * vinogradovKorobovDecayScale X) <
        delta / (3 * (J : ℝ)) := by
    apply (Real.lt_log_iff_exp_lt hdeltaScale).mp
    have ha : 0 < c / 16 := by positivity
    have hmul := mul_lt_mul_of_neg_left hScaleX (neg_lt_zero.mpr ha)
    have hid : -(c / 16) *
        (-Real.log (delta / (3 * (J : ℝ))) / (c / 16)) =
          Real.log (delta / (3 * (J : ℝ))) := by
      field_simp [ha.ne']
    exact hmul.trans_eq hid
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxUpper : x ≤ 2 * X := by
    have hratio : delta / (J : ℝ) ≤ 1 :=
      (div_le_one hJr).2 (hdeltaOne.le.trans hJOne)
    exact hx.1.2.le.trans (by nlinarith)
  have hStrip := norm_halfOpenZeroStripIncrementSum_le_rightEdgeWeight
    (eta := nearOneRightEdgeWidth C 2)
    (sigmaLower := (j : ℝ) / J)
    (sigmaUpper := ((j + 1 : ℕ) : ℝ) / J)
    (T := explicitFormulaHeight J theta X)
    (tau := localTau X theta) (X := X) (x := x)
    hAtRight htau hX hx.1.1 hxUpper
  have hNormSmall :
      ‖halfOpenStripIncrementSum J j
          (explicitFormulaHeight J theta X) (localTau X theta) x‖ <
        delta / (3 * J) * (X / localTau X theta) := by
    rw [halfOpenStripIncrementSum_eq_endpointSum hJ]
    calc
      ‖halfOpenZeroStripIncrementSum ((j : ℝ) / J)
          (((j + 1 : ℕ) : ℝ) / J)
          (explicitFormulaHeight J theta X) (localTau X theta) x‖ ≤
        (2 * X / localTau X theta) *
          rightEdgeZeroWeight (nearOneRightEdgeWidth C 2)
            (explicitFormulaHeight J theta X) X := hStrip
      _ = (X / localTau X theta) *
          (2 * rightEdgeZeroWeight (nearOneRightEdgeWidth C 2)
            (explicitFormulaHeight J theta X) X) := by ring
      _ ≤ (X / localTau X theta) *
          Real.exp (-(c / 16) * vinogradovKorobovDecayScale X) := by gcongr
      _ < (X / localTau X theta) * (delta / (3 * J)) := by
        exact mul_lt_mul_of_pos_left hDecaySmall (div_pos hXPos htau)
      _ = delta / (3 * J) * (X / localTau X theta) := by ring
  exact (not_le_of_gt hNormSmall) hx.2

/-- Power-bound form of the right-edge strip alternative. -/
theorem equation27StripMeasure_epsilonBound_of_rightEdge
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {J j : ℕ} (hJ : 0 < J)
    {theta delta q : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hAtRight : 1 - nearOneRightEdgeWidth C 2 ≤ (j : ℝ) / J) :
    EpsilonExponentBound
      (fun X => equation27StripMeasure J j theta delta X) q :=
  equation27StripMeasure_epsilonBound_of_eventually_empty
    (eventually_equation27StripLargeSet_eq_empty_of_rightEdge
      hDensity hZeroFree hC hc hJ hthetaLower hthetaUpper
        hdelta hdeltaOne hAtRight)

end GafniTao

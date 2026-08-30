import GafniTao.Equation27
import GafniTao.ExceptionalEntry

/-!
# The source epsilon and strip-count limits

This file spends the two strict margins which remain after the finite
equation-(2.7) assembly.  It does not assume continuity or attainment of the
zero-density envelopes: the source infimum supplies a positive epsilon
witness, an intermediate real exponent supplies the first strict margin, and
an Archimedean choice of `J` absorbs both the right-edge and `4 / J` losses.
-/

namespace GafniTao

/-- Choose one positive natural strip count satisfying two independent
inverse-power budgets. -/
theorem exists_positive_nat_with_inverse_margins
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ J : ℕ, 0 < J ∧ 1 / (J : ℝ) < a ∧ 4 / (J : ℝ) < b := by
  have hquarter : 0 < b / 4 := div_pos hb (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min ha hquarter)
  have hn' : 1 / (((n + 1 : ℕ) : ℝ)) < min a (b / 4) := by
    simpa [Nat.cast_add, Nat.cast_one] using hn
  refine ⟨n + 1, Nat.succ_pos n, hn'.trans_le (min_le_left _ _), ?_⟩
  have hnQuarter : 1 / ((n + 1 : ℕ) : ℝ) < b / 4 :=
    hn'.trans_le (min_le_right _ _)
  have hfour : (0 : ℝ) < 4 := by norm_num
  calc
    4 / ((n + 1 : ℕ) : ℝ) = 4 * (1 / ((n + 1 : ℕ) : ℝ)) := by ring
    _ < 4 * (b / 4) := mul_lt_mul_of_pos_left hnQuarter hfour
    _ = b := by ring

/-- The same Archimedean choice with an additional prescribed natural lower
bound.  This is needed because the explicit formula and local replacement
have fixed constants which must be paid before the inverse strip losses are
sent to zero. -/
theorem exists_nat_ge_with_inverse_margins
    (J₀ : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ J : ℕ, J₀ ≤ J ∧ 0 < J ∧ 1 / (J : ℝ) < a ∧ 4 / (J : ℝ) < b := by
  obtain ⟨K, hK, hKa, hKb⟩ :=
    exists_positive_nat_with_inverse_margins ha hb
  let J := max J₀ K
  have hKJ : K ≤ J := le_max_right J₀ K
  have hJ : 0 < J := hK.trans_le hKJ
  have hInv : 1 / (J : ℝ) ≤ 1 / (K : ℝ) := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast hK
    · exact_mod_cast hKJ
  refine ⟨J, le_max_left J₀ K, hJ, hInv.trans_lt hKa, ?_⟩
  have hFourInv : 4 / (J : ℝ) ≤ 4 / (K : ℝ) := by
    calc
      4 / (J : ℝ) = 4 * (1 / (J : ℝ)) := by ring
      _ ≤ 4 * (1 / (K : ℝ)) := by gcongr
      _ = 4 / (K : ℝ) := by ring
  exact hFourInv.trans_lt hKb

/-- Strictly lying above the literal source infimum yields a smaller positive
source epsilon, a still-positive density threshold, and a finite real
exponent strictly between the fixed-epsilon supremum and the requested
target. -/
theorem exists_refined_limit_witness
    {theta xi : ℝ} (htheta : theta < 1)
    (hrefined : refinedExceptionalUpperExponent theta < (xi : EReal)) :
    ∃ eps mu : ℝ,
      0 < eps ∧
      0 < 1 / (1 - theta) - eps ∧
      refinedFixedEpsilonExponent theta eps < (mu : EReal) ∧
      mu < xi := by
  obtain ⟨x, hx, hxXi⟩ := sInf_lt_iff.mp hrefined
  rcases hx with ⟨eps₀, heps₀, rfl⟩
  let eps : ℝ := min eps₀ (1 / (2 * (1 - theta)))
  have hgap : 0 < 1 - theta := sub_pos.mpr htheta
  have hcap : 0 < 1 / (2 * (1 - theta)) := by positivity
  have heps : 0 < eps := lt_min heps₀ hcap
  have hepsLe : eps ≤ eps₀ := min_le_left _ _
  have hfixedXi : refinedFixedEpsilonExponent theta eps < (xi : EReal) :=
    (refinedFixedEpsilonExponent_mono hepsLe).trans_lt hxXi
  obtain ⟨mu, hfixedMu, hmuXi⟩ := EReal.exists_between_coe_real hfixedXi
  refine ⟨eps, mu, heps, ?_, hfixedMu, by exact_mod_cast hmuXi⟩
  have hepsCap : eps ≤ 1 / (2 * (1 - theta)) := min_le_right _ _
  have hhalf : 1 / (2 * (1 - theta)) < 1 / (1 - theta) := by
    have hdenom : 0 < 1 - theta := hgap
    calc
      1 / (2 * (1 - theta)) = (1 / 2 : ℝ) * (1 / (1 - theta)) := by
        field_simp [hdenom.ne']
      _ < 1 * (1 / (1 - theta)) := by
        gcongr
        norm_num
      _ = 1 / (1 - theta) := one_mul _
  linarith

/-- The complete `epsilon -> 0`, `J -> infinity` consumer for the literal
full-zero event occurring in equation (2.7).  The conclusion is a genuine
fixed-power estimate with no epsilon in its definition.  The only analytic
premises are the exact near-one logarithmic density and
Vinogradov--Korobov vanishing predicates used by the right-edge branch. -/
theorem equation27FullZeroMeasure_fixedPowerBound_of_refined_lt
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta delta xi : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsource :
      max (((1 - theta : ℝ) : EReal))
          (refinedExceptionalUpperExponent theta) < (xi : EReal)) :
    ∃ J : ℕ, 0 < J ∧
      FixedPowerBound
        (fun X => equation27FullZeroMeasure J theta delta X) xi := by
  have hparts := max_lt_iff.mp hsource
  obtain ⟨eps, mu, heps, hthreshold, hfixed, hmuXi⟩ :=
    exists_refined_limit_witness hthetaUpper hparts.2
  have hbaseXi : 1 - theta < xi := by exact_mod_cast hparts.1
  have hmaxXi : max (1 - theta) mu < xi := max_lt hbaseXi hmuXi
  have hrightMargin :
      0 < eps * (1 - theta) * nearOneRightEdgeWidth C 2 := by
    exact mul_pos (mul_pos heps (sub_pos.mpr hthetaUpper))
      (nearOneRightEdgeWidth_pos hC (by norm_num))
  have hpowerMargin : 0 < xi - max (1 - theta) mu :=
    sub_pos.mpr hmaxXi
  obtain ⟨J, hJ, hJRight, hJPower⟩ :=
    exists_positive_nat_with_inverse_margins hrightMargin hpowerMargin
  refine ⟨J, hJ, ?_⟩
  have hEpsilon :=
    equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs
      cutoff hDensity hZeroFree hC hc hJ hthetaLower hthetaUpper heps
        hthreshold hdelta hdeltaOne hJRight hfixed
  apply fixedPowerBound_of_epsilonExponentBound_lt hEpsilon
  linarith

/-- Extended-real exponent form of the preceding fixed-power theorem. -/
theorem leastFixedPowerExponent_equation27FullZeroMeasure_lt
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta delta xi : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsource :
      max (((1 - theta : ℝ) : EReal))
          (refinedExceptionalUpperExponent theta) < (xi : EReal)) :
    ∃ J : ℕ, 0 < J ∧
      leastFixedPowerExponent
          (fun X => equation27FullZeroMeasure J theta delta X) ≤
        (xi : EReal) := by
  obtain ⟨J, hJ, hBound⟩ :=
    equation27FullZeroMeasure_fixedPowerBound_of_refined_lt cutoff
      hDensity hZeroFree hC hc hthetaLower hthetaUpper hdelta hdeltaOne
        hsource
  exact ⟨J, hJ, leastFixedPowerExponent_le hBound⟩

/-- Complete local-interval form of the Gafni--Tao exponent deduction.  This
is the first theorem in the chain whose left side is an actual Mangoldt
exceptional measure.  It remains conditional only on the three precise
published analytic inputs which are not yet proved in this package. -/
theorem localExceptionalMeasure_fixedPowerBound_of_source_inputs
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta delta xi : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsource :
      max (((1 - theta : ℝ) : EReal))
          (refinedExceptionalUpperExponent theta) < (xi : EReal)) :
    ∃ J : ℕ, 0 < J ∧
      FixedPowerBound
        (fun X => localShortIntervalExceptionalMeasure J theta delta X) xi := by
  obtain ⟨CFormula, hCFormula, hTransfer⟩ :=
    localExceptionalMeasure_fixedPowerBound_of_equation27 hFormula
  obtain ⟨eps, mu, heps, hthreshold, hfixed, hmuXi⟩ :=
    exists_refined_limit_witness hthetaUpper (max_lt_iff.mp hsource).2
  have hbaseXi : 1 - theta < xi := by
    exact_mod_cast (max_lt_iff.mp hsource).1
  have hmaxXi : max (1 - theta) mu < xi := max_lt hbaseXi hmuXi
  obtain ⟨J₀, hJ₀⟩ := exists_nat_gt
    (max (6 * (8 / theta + 2)) (24 * CFormula / delta))
  have hrightMargin :
      0 < eps * (1 - theta) * nearOneRightEdgeWidth C 2 := by
    exact mul_pos (mul_pos heps (sub_pos.mpr hthetaUpper))
      (nearOneRightEdgeWidth_pos hC (by norm_num))
  have hpowerMargin : 0 < xi - max (1 - theta) mu :=
    sub_pos.mpr hmaxXi
  obtain ⟨J, hJ₀J, hJ, hJRight, hJPower⟩ :=
    exists_nat_ge_with_inverse_margins J₀ hrightMargin hpowerMargin
  have hJLowerReal : (J₀ : ℝ) ≤ J := by exact_mod_cast hJ₀J
  have hJLocal : 6 * (8 / theta + 2) ≤ (J : ℝ) := by
    exact (le_max_left _ _).trans (hJ₀.le.trans hJLowerReal)
  have hJFormula : 24 * CFormula ≤ delta * (J : ℝ) := by
    have hRatio : 24 * CFormula / delta ≤ (J : ℝ) :=
      (le_max_right _ _).trans (hJ₀.le.trans hJLowerReal)
    have hRaw : 24 * CFormula ≤ (J : ℝ) * delta :=
      (div_le_iff₀ hdelta).mp hRatio
    simpa [mul_comm] using hRaw
  have hEquationEpsilon :=
    equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs
      cutoff hDensity hZeroFree hC hc hJ hthetaLower hthetaUpper heps
        hthreshold hdelta hdeltaOne hJRight hfixed
  have hEquationFixed :
      FixedPowerBound
        (fun X => equation27FullZeroMeasure J theta delta X) xi :=
    fixedPowerBound_of_epsilonExponentBound_lt hEquationEpsilon (by linarith)
  refine ⟨J, hJ, ?_⟩
  exact hTransfer hJ hthetaLower hthetaUpper hdelta hdeltaOne hJLocal
    hJFormula hEquationFixed

end GafniTao

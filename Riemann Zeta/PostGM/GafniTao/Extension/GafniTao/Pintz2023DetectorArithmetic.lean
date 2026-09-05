import GafniTao.Pintz2023Arithmetic
import GafniTao.Pintz2023CorollaryOneAlgebra
import GafniTao.Pintz2023DetectionEventualNative

/-!
# Strict source margins for Pintz's detector

The cell inequality `eta*k*(k-1) < 1` gives the strict Gaussian power
saving used in (4.11).  It is proved before choosing the auxiliary epsilon,
so all later losses can be budgeted against a genuine open margin.
-/

namespace GafniTao

noncomputable section

theorem pintzCell_detector_base_exponent_neg
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    (1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) -
        2 * eta / (k : ℝ) < 0 := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  rcases hcell with ⟨hkFour, _hellThree, hkUpper, _hkLower,
    _hellUpper, _hellLower⟩
  have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hkFour
  have hkPos : (0 : ℝ) < k := by linarith
  have hkCompare : (k : ℝ) ≤ 2 * ((k : ℝ) - 1) := by linarith
  have hetaKSq : eta * (k : ℝ) ^ 2 < 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hkCompare
      (mul_nonneg heta.le hkPos.le)
    nlinarith
  have hsq : 2 * eta < (2 / (k : ℝ)) ^ 2 := by
    rw [div_pow]
    apply (lt_div_iff₀ (sq_pos_of_pos hkPos)).2
    nlinarith
  have hsqrt : Real.sqrt (2 * eta) < 2 / (k : ℝ) := by
    exact (Real.sqrt_lt' (div_pos (by norm_num) hkPos)).2 hsq
  rw [eta_three_halves_eq_eta_mul_sqrt (by positivity : 0 ≤ 2 * eta)]
  have hmul := mul_lt_mul_of_pos_left hsqrt heta
  calc
    (1 / 2 : ℝ) * (2 * eta * Real.sqrt (2 * eta)) -
          2 * eta / (k : ℝ) =
        eta * Real.sqrt (2 * eta) - eta * (2 / (k : ℝ)) := by ring
    _ < 0 := sub_neg.mpr hmul

theorem pintz2023DetectorExponent_eq_base_add
    (eta epsilon : ℝ) (k ell : ℕ) :
    pintz2023DetectorExponent eta epsilon epsilon k ell =
      ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) -
        2 * eta / (k : ℝ)) +
      epsilon * (1 + eta / (5 * (ell : ℝ))) := by
  unfold pintz2023DetectorExponent
  ring

theorem pintzPerturbedCoefficient_mono_epsilon
    {eta epsilon₁ epsilon₂ : ℝ} {k ell : ℕ}
    (hepsilon : epsilon₁ ≤ epsilon₂)
    (hk : 0 < k) (hell : 0 < ell)
    (hkMargin : 6 * (k : ℝ) * epsilon₂ <
      1 - ((k : ℝ) - 1) * eta)
    (hellMargin : 6 * (ell : ℝ) * epsilon₂ <
      1 - 2 * eta * ((ell : ℝ) - 1)) :
    pintzPerturbedCoefficient eta epsilon₁ k ell ≤
      pintzPerturbedCoefficient eta epsilon₂ k ell := by
  have hkPos₂ := pintzKDenominator_pos hk hkMargin
  have hellPos₂ := pintzEllDenominator_pos hell hellMargin
  have hkMono : pintzKDenominator eta epsilon₂ k ≤
      pintzKDenominator eta epsilon₁ k := by
    unfold pintzKDenominator
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hscaled := mul_le_mul_of_nonneg_left hepsilon (sq_nonneg (k : ℝ))
    nlinarith
  have hellMono : pintzEllDenominator eta epsilon₂ ell ≤
      pintzEllDenominator eta epsilon₁ ell := by
    unfold pintzEllDenominator
    have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
    have hscaled := mul_le_mul_of_nonneg_left hepsilon (sq_nonneg (ell : ℝ))
    nlinarith
  unfold pintzPerturbedCoefficient
  exact max_le_max
    (div_le_div_of_nonneg_left (by norm_num) hellPos₂ hellMono)
    (div_le_div_of_nonneg_left (by norm_num) hkPos₂ hkMono)

/-- Choose Pintz's single auxiliary epsilon with simultaneous reserves for
the final exponent, both Section-3 denominator windows, the source cutoff,
the zeta-growth estimate, and the strict detector decay. -/
theorem exists_pintz_source_perturbation
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (htarget : 0 < target) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧
      epsilon / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ) ∧
      pintz2023DetectorExponent eta epsilon epsilon k ell < 0 ∧
      eta + 6 * epsilon < pintz2023HBAlpha k ∧
      2 * eta + 6 * epsilon < pintz2023HBAlpha ell ∧
      6 * (k : ℝ) * epsilon < 1 - ((k : ℝ) - 1) * eta ∧
      6 * (ell : ℝ) * epsilon <
        1 - 2 * eta * ((ell : ℝ) - 1) ∧
      eta * pintzPerturbedCoefficient eta epsilon k ell <
        eta * pintzTheoremOneCoefficient eta k ell + target := by
  have heta := pintzCell_eta_pos hcell
  have hk : 0 < k := lt_of_lt_of_le (by omega) hcell.1
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  have hkMinusOne : (0 : ℝ) < (k : ℝ) - 1 := by
    have hkFour : (4 : ℝ) ≤ k := by exact_mod_cast hcell.1
    linarith
  have hellMinusOne : (0 : ℝ) < (ell : ℝ) - 1 := by
    have hellThree : (3 : ℝ) ≤ ell := by exact_mod_cast hcell.2.1
    linarith
  have hkAlphaGap : 0 < pintz2023HBAlpha k - eta := by
    rw [sub_pos]
    unfold pintz2023HBAlpha
    rw [lt_div_iff₀ (mul_pos hkReal hkMinusOne)]
    simpa [mul_assoc] using hcell.2.2.1
  have hellAlphaGap : 0 < pintz2023HBAlpha ell - 2 * eta := by
    rw [sub_pos]
    unfold pintz2023HBAlpha
    rw [lt_div_iff₀ (mul_pos hellReal hellMinusOne)]
    nlinarith [hcell.2.2.2.2.1]
  let base : ℝ := (1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) -
    2 * eta / (k : ℝ)
  have hbase : base < 0 := by
    exact pintzCell_detector_base_exponent_neg hcell
  let slope : ℝ := 1 + eta / (5 * (ell : ℝ))
  have hslope : 0 < slope := by dsimp only [slope]; positivity
  let cutoffCap : ℝ := 20 * (ell : ℝ) / (k : ℝ)
  have hcutoffCap : 0 < cutoffCap := by dsimp only [cutoffCap]; positivity
  let decayCap : ℝ := -base / (2 * slope)
  have hdecayCap : 0 < decayCap := by
    dsimp only [decayCap]
    exact div_pos (neg_pos.mpr hbase) (mul_pos (by norm_num) hslope)
  let kAlphaCap : ℝ := (pintz2023HBAlpha k - eta) / 12
  have hkAlphaCap : 0 < kAlphaCap := by
    dsimp only [kAlphaCap]
    positivity
  let ellAlphaCap : ℝ := (pintz2023HBAlpha ell - 2 * eta) / 12
  have hellAlphaCap : 0 < ellAlphaCap := by
    dsimp only [ellAlphaCap]
    positivity
  let cap : ℝ := min 1
    (min cutoffCap (min decayCap (min kAlphaCap ellAlphaCap)))
  have hcap : 0 < cap := by dsimp only [cap]; positivity
  obtain ⟨epsilon₀, hepsilon₀, hkMargin₀, hellMargin₀, hCoeff₀⟩ :=
    exists_pintz_perturbation hcell htarget
  let epsilon : ℝ := min epsilon₀ cap / 2
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hepsilonLe₀ : epsilon ≤ epsilon₀ := by
    dsimp only [epsilon]
    have := min_le_left epsilon₀ cap
    nlinarith
  have hepsilonCap : epsilon < cap := by
    dsimp only [epsilon]
    have := min_le_right epsilon₀ cap
    nlinarith
  have hcapOne : cap ≤ 1 := by dsimp only [cap]; exact min_le_left _ _
  have hcapCutoff : cap ≤ cutoffCap := by
    dsimp only [cap]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcapDecay : cap ≤ decayCap := by
    dsimp only [cap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hcapKAlpha : cap ≤ kAlphaCap := by
    dsimp only [cap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hcapEllAlpha : cap ≤ ellAlphaCap := by
    dsimp only [cap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hepsilonOne : epsilon ≤ 1 := (le_of_lt hepsilonCap).trans hcapOne
  have hepsilonCutoff : epsilon ≤ cutoffCap :=
    (le_of_lt hepsilonCap).trans hcapCutoff
  have hcutoff : epsilon / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 10 * ell) hkReal]
    dsimp only [cutoffCap] at hepsilonCutoff
    have := (le_div_iff₀ hkReal).mp hepsilonCutoff
    nlinarith
  have hepsilonDecay : epsilon < decayCap :=
    hepsilonCap.trans_le hcapDecay
  have hdecay : pintz2023DetectorExponent eta epsilon epsilon k ell < 0 := by
    rw [pintz2023DetectorExponent_eq_base_add]
    change base + epsilon * slope < 0
    dsimp only [decayCap] at hepsilonDecay
    have hmul := mul_lt_mul_of_pos_right hepsilonDecay hslope
    field_simp [hslope.ne'] at hmul
    nlinarith
  have hkAlphaMargin : eta + 6 * epsilon < pintz2023HBAlpha k := by
    have hepsilonKAlpha : epsilon < kAlphaCap :=
      hepsilonCap.trans_le hcapKAlpha
    dsimp only [kAlphaCap] at hepsilonKAlpha
    nlinarith
  have hellAlphaMargin : 2 * eta + 6 * epsilon <
      pintz2023HBAlpha ell := by
    have hepsilonEllAlpha : epsilon < ellAlphaCap :=
      hepsilonCap.trans_le hcapEllAlpha
    dsimp only [ellAlphaCap] at hepsilonEllAlpha
    nlinarith
  have hkMargin : 6 * (k : ℝ) * epsilon <
      1 - ((k : ℝ) - 1) * eta := by
    nlinarith
  have hellMargin : 6 * (ell : ℝ) * epsilon <
      1 - 2 * eta * ((ell : ℝ) - 1) := by
    nlinarith
  have hCoeffMono := pintzPerturbedCoefficient_mono_epsilon
    hepsilonLe₀ hk hell hkMargin₀ hellMargin₀
  have hCoeff : eta * pintzPerturbedCoefficient eta epsilon k ell <
      eta * pintzTheoremOneCoefficient eta k ell + target := by
    have := mul_le_mul_of_nonneg_left hCoeffMono heta.le
    exact this.trans_lt hCoeff₀
  exact ⟨epsilon, hepsilon, hepsilonOne, hcutoff, hdecay,
    hkAlphaMargin, hellAlphaMargin, hkMargin, hellMargin, hCoeff⟩

#print axioms pintzCell_detector_base_exponent_neg
#print axioms pintz2023DetectorExponent_eq_base_add
#print axioms pintzPerturbedCoefficient_mono_epsilon
#print axioms exists_pintz_source_perturbation

end

end GafniTao

import GafniTao.Pintz2023Equation420Complete
import GafniTao.Pintz2023SmallBComplete
import GafniTao.Pintz2023CriticalScaleMonotone
import GafniTao.Pintz2023GramSymmetry

/-!
# Pintz (2023), equation (4.19): the two Gram ranges

The split is made at the literal source threshold
`N = |delta-gamma|^(1.9/ell)`.  Corollary 3 handles the lower block-length
range, while the completed equation-(4.20) estimate handles its complement.
-/

open Complex Filter

namespace GafniTao

noncomputable section

/-- Uniform energy-weighted off-diagonal Gram estimate after the exact
small/large local-frequency split in equations (4.20)--(4.23). -/
theorem exists_pintz2023_equation419_offDiagonal_gram_native
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∃ N₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (etaJ etaK gamma delta T : ℝ),
      N₀ ≤ N → etaJ ∈ Set.Icc 0 eta → etaK ∈ Set.Icc 0 eta →
      1 ≤ |delta - gamma| → |delta - gamma| ≤ T → 1 ≤ T →
      T ^ pintz2023EllThreshold eta data.epsilon ell ≤ (N : ℝ) →
      (N : ℝ) ≤ T ^ (3 : ℝ) →
      3 * pintz2023SourceLambda T k ≤ |delta - gamma| →
      (N : ℝ) ^ (-4 * eta) *
          ‖pintz2023SmoothedZetaSum N
            (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
              I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
        4 * (N : ℝ) ^ (-2 * data.epsilon) +
          C * (4 * eta)⁻¹ *
            ((4 ^ pintz2023NearOneGramExponent
                eta eta data.epsilon + 3) *
              T ^ (-data.epsilon / (k : ℝ))) := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hellNat : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hellPos : (0 : ℝ) < ell := by exact_mod_cast hellNat
  have hepsilonScaled :
      data.epsilon * (100 * (ell : ℝ)) ≤ eta := by
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 100 * (ell : ℝ))).mp
      data.equation420_small
  have hepsilonThree : 3 * data.epsilon ≤ 1 := by
    have hellReal : (3 : ℝ) ≤ ell := by exact_mod_cast hcell.2.1
    nlinarith [data.eta_le_one_twentyFour]
  have hTarget : 2 * data.epsilon ≤ 4 * eta := by
    have hone : (1 : ℝ) ≤ 100 * (ell : ℝ) := by
      have : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
      nlinarith
    have hepsilonEta : data.epsilon ≤ eta :=
      (calc
        data.epsilon ≤ data.epsilon * (100 * (ell : ℝ)) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hone data.epsilon_pos.le
        _ ≤ eta := hepsilonScaled)
    linarith
  obtain ⟨_C₀, _C₁, _hC₀, _hC₁, hSmallEventually⟩ :=
    eventually_pintz2023_smallB_complete_gram_native
      ell eta data.epsilon hcell.2.1 heta.le data.epsilon_pos
        hepsilonThree hTarget
  obtain ⟨N₀, hSmall⟩ := eventually_atTop.1 hSmallEventually
  obtain ⟨C, hC, hLarge⟩ :=
    exists_pintz2023_equation420_gram_native hcell data
  refine ⟨N₀, C, hC, ?_⟩
  intro N etaJ etaK gamma delta T hN₀ hetaJ hetaK hSep hDifference
    hT hCritical hNUpper hSelectedSep
  have hNPos : 0 < N := by
    have hCriticalOne : 1 ≤
        T ^ pintz2023EllThreshold eta data.epsilon ell := by
      have hExponent : 0 ≤
          pintz2023EllThreshold eta data.epsilon ell := by
        unfold pintz2023EllThreshold
        exact one_div_nonneg.mpr
          (pintzEllDenominator_pos
            hellNat data.ell_margin).le
      exact Real.one_le_rpow hT hExponent
    have : (1 : ℝ) ≤ N := hCriticalOne.trans hCritical
    have hNOne : 1 ≤ N := by exact_mod_cast this
    exact Nat.zero_lt_one.trans_le hNOne
  have hXiNonneg : 0 ≤ etaJ + etaK := by
    linarith [hetaJ.1, hetaK.1]
  have hXiUpper : etaJ + etaK ≤ 2 * eta := by
    linarith [hetaJ.2, hetaK.2]
  have hReal : 0 ≤ 1 - ((etaJ + etaK) + 4 * eta) := by
    linarith [data.eta_le_one_twentyFour, hetaJ.2, hetaK.2]
  have hAlpha : etaJ + etaK ≤
      pintz2023HBAlpha ell - 6 * data.epsilon := by
    linarith [data.ell_alpha]
  have hDen : 0 <
      1 - ((ell : ℝ) - 1) * (etaJ + etaK) -
        6 * (ell : ℝ) * data.epsilon := by
    have hellMinus : 0 ≤ (ell : ℝ) - 1 := by
      have : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hXiUpper hellMinus
    linarith [data.ell_margin]
  have hCriticalEq :
      pintz2023CriticalScale ell (2 * eta) data.epsilon T =
        T ^ pintz2023EllThreshold eta data.epsilon ell := by
    unfold pintz2023CriticalScale pintz2023CriticalScaleExponent
      pintz2023EllThreshold pintzEllDenominator
    congr 1
    ring_nf
  have hCriticalSum :
      pintz2023CriticalScale ell (etaJ + etaK) data.epsilon T ≤
        (N : ℝ) := by
    calc
      pintz2023CriticalScale ell (etaJ + etaK) data.epsilon T ≤
          pintz2023CriticalScale ell (2 * eta) data.epsilon T :=
        pintz2023CriticalScale_mono_xi
          hellNat hXiUpper hT (by linarith [data.ell_margin])
      _ = T ^ pintz2023EllThreshold eta data.epsilon ell := hCriticalEq
      _ ≤ (N : ℝ) := hCritical
  have hSmallTermNonneg : 0 ≤ 4 * (N : ℝ) ^ (-2 * data.epsilon) := by
    positivity
  have hLargeTermNonneg : 0 ≤
      C * (4 * eta)⁻¹ *
        ((4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) *
          T ^ (-data.epsilon / (k : ℝ))) := by
    positivity
  by_cases hRange : (N : ℝ) ≤
      |delta - gamma| ^ (19 / (10 * (ell : ℝ)))
  · have hSmallRaw := hSmall N hN₀ (etaJ + etaK)
      |delta - gamma| T hXiNonneg hReal hAlpha hDen hSep hDifference
      hT hCriticalSum hRange
    rw [norm_pintz2023SmoothedZetaSum_abs_im N
      (1 - etaJ - etaK - 4 * eta) (delta - gamma)]
    have hArgument :
        (((1 - ((etaJ + etaK) + 4 * eta) : ℝ) : ℂ) +
            I * ((|delta - gamma| : ℝ) : ℂ)) =
          (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
            I * ((|delta - gamma| : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring_nf
    rw [← hArgument]
    have hNRealPos : (0 : ℝ) < N := by exact_mod_cast hNPos
    calc
      (N : ℝ) ^ (-4 * eta) *
          ‖pintz2023SmoothedZetaSum N
            (((1 - ((etaJ + etaK) + 4 * eta) : ℝ) : ℂ) +
              I * ((|delta - gamma| : ℝ) : ℂ))‖ ≤
        (N : ℝ) ^ (-4 * eta) *
          (4 * (N : ℝ) ^ (4 * eta - 2 * data.epsilon)) := by
        gcongr
      _ = 4 * (N : ℝ) ^ (-2 * data.epsilon) := by
        calc
          (N : ℝ) ^ (-4 * eta) *
              (4 * (N : ℝ) ^ (4 * eta - 2 * data.epsilon)) =
            4 * ((N : ℝ) ^ (-4 * eta) *
              (N : ℝ) ^ (4 * eta - 2 * data.epsilon)) := by ring_nf
          _ = 4 * (N : ℝ) ^
              (-4 * eta + (4 * eta - 2 * data.epsilon)) := by
            rw [← Real.rpow_add hNRealPos]
          _ = 4 * (N : ℝ) ^ (-2 * data.epsilon) := by ring_nf
      _ ≤ 4 * (N : ℝ) ^ (-2 * data.epsilon) +
          C * (4 * eta)⁻¹ *
            ((4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) *
              T ^ (-data.epsilon / (k : ℝ))) :=
        le_add_of_nonneg_right hLargeTermNonneg
  · have hFrequency :
        |delta - gamma| ^ (19 / (10 * (ell : ℝ))) ≤ (N : ℝ) :=
      le_of_not_ge hRange
    exact (hLarge N etaJ etaK gamma delta T hNPos hetaJ hetaK hSep hT
      hCritical hFrequency hNUpper hSelectedSep).trans
        (le_add_of_nonneg_left hSmallTermNonneg)

#print axioms exists_pintz2023_equation419_offDiagonal_gram_native

end

end GafniTao

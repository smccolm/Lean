import GafniTao.Pintz2023SmallBComplete
import GafniTao.Pintz2023NearOneGramBounds
import GafniTao.Pintz2023CriticalScaleMonotone
import GafniTao.Pintz2023GramSymmetry

/-!
# Pintz (2023), the two off-diagonal Gram ranges after equation (4.19)

The split is made at the literal source threshold
`N = |delta - gamma|^(1.9/r)`.  In the large-frequency range the complete
Corollary-2/3 argument is used.  In the complementary range the global
smoothed-zeta estimate is retained.  The two resulting majorants remain
separate for the energy absorption following equation (4.20).
-/

open Complex Filter

namespace GafniTao

noncomputable section

/-- Source-faithful two-range bound for an off-diagonal entry of the Gram
matrix.  The natural threshold supplied by the eventual small-`B_h` theorem
is returned explicitly. -/
theorem exists_pintz2023_split_offDiagonal_gram_native
    (r : ℕ) (eta epsilon : ℝ) (hr : 3 ≤ r)
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hepsilonUpper : 3 * epsilon ≤ 1)
    (hTarget : 2 * epsilon ≤ 4 * eta) :
    ∃ N₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (xi etaJ etaK gamma delta T G : ℝ),
        N₀ ≤ N →
        etaJ ∈ Set.Icc 0 xi → etaK ∈ Set.Icc 0 xi →
        2 * xi + 6 * epsilon ≤ pintz2023HBAlpha r →
        6 * (r : ℝ) * epsilon <
          1 - ((r : ℝ) - 1) * (2 * xi) →
        pintz2023NearOneGramMaxDistance xi eta ≤ 1 / 4 →
        1 ≤ T → 1 ≤ G → |gamma| ≤ T → |delta| ≤ T →
        G ≤ |delta - gamma| →
        pintz2023CriticalScale r (2 * xi) epsilon (2 * T + 3) ≤
          (N : ℝ) →
        ‖pintz2023SmoothedZetaSum N
            (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
              I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
          4 * (N : ℝ) ^ (4 * eta - 2 * epsilon) +
            pintz2023NearOneOffDiagonalMajorant
              C N xi eta epsilon T G := by
  obtain ⟨_C₀, _C₁, _hC₀, _hC₁, hSmallEventually⟩ :=
    eventually_pintz2023_smallB_complete_gram_native
      r eta epsilon hr heta.le hepsilon hepsilonUpper hTarget
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 hSmallEventually)
  obtain ⟨C, hC, hLarge⟩ :=
    exists_pintz2023NearOneOffDiagonalMajorant hepsilon
      (by linarith : epsilon ≤ 1)
  refine ⟨N₀, C, hC, ?_⟩
  intro N xi etaJ etaK gamma delta T G hN hetaJ hetaK
    hAlpha hDen hMax hT hG hgamma hdelta hSeparated hCritical
  have hrPos : 0 < r := by omega
  have hrMinus : 0 ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    linarith
  have hXiSumNonneg : 0 ≤ etaJ + etaK := by
    linarith [hetaJ.1, hetaK.1]
  have hXiSumUpper : etaJ + etaK ≤ 2 * xi := by
    linarith [hetaJ.2, hetaK.2]
  have hAlphaSum : etaJ + etaK ≤
      pintz2023HBAlpha r - 6 * epsilon := by
    linarith
  have hDenSum : 0 <
      1 - ((r : ℝ) - 1) * (etaJ + etaK) -
        6 * (r : ℝ) * epsilon := by
    have hmul := mul_le_mul_of_nonneg_left hXiSumUpper hrMinus
    linarith
  have hReal : 0 ≤ 1 - ((etaJ + etaK) + 4 * eta) := by
    unfold pintz2023NearOneGramMaxDistance at hMax
    linarith [hetaJ.2, hetaK.2]
  have hDifferenceUpper : |delta - gamma| ≤ 2 * T := by
    calc
      |delta - gamma| ≤ |delta| + |gamma| := abs_sub delta gamma
      _ ≤ T + T := add_le_add hdelta hgamma
      _ = 2 * T := by ring
  have hDifferenceUpper' : |delta - gamma| ≤ 2 * T + 3 := by linarith
  have hDifferenceOne : 1 ≤ |delta - gamma| := hG.trans hSeparated
  have hHeight : 1 ≤ 2 * T + 3 := by linarith
  have hCriticalSum :
      pintz2023CriticalScale r (etaJ + etaK) epsilon (2 * T + 3) ≤
        (N : ℝ) :=
    (pintz2023CriticalScale_mono_xi hrPos hXiSumUpper hHeight
      (by linarith)).trans hCritical
  have hNReal : (1 : ℝ) ≤ (N : ℝ) :=
    (one_le_pintz2023CriticalScale hrPos hHeight (by linarith)).trans
      hCritical
  have hNPositive : 0 < N := by exact_mod_cast hNReal
  have hLargeMajorantNonneg : 0 ≤
      pintz2023NearOneOffDiagonalMajorant C N xi eta epsilon T G := by
    unfold pintz2023NearOneOffDiagonalMajorant
    positivity
  by_cases hRange : (N : ℝ) ≤
      |delta - gamma| ^ (19 / (10 * (r : ℝ)))
  · have hSmall := hN₀ N hN (etaJ + etaK) |delta - gamma|
      (2 * T + 3) hXiSumNonneg hReal hAlphaSum hDenSum
      hDifferenceOne hDifferenceUpper' hHeight hCriticalSum hRange
    rw [norm_pintz2023SmoothedZetaSum_abs_im N
      (1 - etaJ - etaK - 4 * eta) (delta - gamma)]
    have hArgument :
        (((1 - ((etaJ + etaK) + 4 * eta) : ℝ) : ℂ) +
            I * ((|delta - gamma| : ℝ) : ℂ)) =
          (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
            I * ((|delta - gamma| : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [← hArgument]
    exact hSmall.trans (le_add_of_nonneg_right hLargeMajorantNonneg)
  · have hLargeEntry := hLarge N xi eta etaJ etaK gamma delta T G
      hNPositive heta hetaJ hetaK hMax hT hG hgamma hdelta
      hSeparated
    exact hLargeEntry.trans (le_add_of_nonneg_left (by positivity))

#print axioms exists_pintz2023_split_offDiagonal_gram_native

end

end GafniTao

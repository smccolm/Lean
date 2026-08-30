import GafniTao.StripAssembly
import GafniTao.CriticalStripSymmetry

/-!
# The exact Gafni--Tao refined exponent

This file records the extended-real right side of Theorem 1.3 literally.  In
particular the positive-`epsilon` infimum is retained and the supremum is a
complete-lattice supremum, so an empty admissible set has value `-infinity`.
-/

namespace GafniTao

/-- The source second-moment exponent
`(1-theta)(1-sigma) A(sigma) + 2 sigma - 1`. -/
noncomputable def ordinaryMomentExponent (theta sigma : ℝ) : EReal :=
  (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
      zeroDensityExponent sigma + ((2 * sigma - 1 : ℝ) : EReal)

/-- The source fourth-moment exponent
`(1-theta)(1-sigma) A*(sigma) + 4 sigma - 3`. -/
noncomputable def additiveEnergyMomentExponent (theta sigma : ℝ) : EReal :=
  (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
      zeroAdditiveEnergyExponent sigma + ((4 * sigma - 3 : ℝ) : EReal)

/-- The exact sigma constraint under the supremum in Theorem 1.3. -/
def RefinedSigmaAdmissible (theta eps sigma : ℝ) : Prop :=
  0 ≤ sigma ∧ sigma < 1 ∧
    ((1 / (1 - theta) - eps : ℝ) : EReal) ≤ zeroDensityExponent sigma

/-- The fixed-`epsilon` supremum in Gafni--Tao Theorem 1.3.  Since `EReal`
is a complete linear order, the empty supremum is definitionally `⊥`. -/
noncomputable def refinedFixedEpsilonExponent (theta eps : ℝ) : EReal :=
  sSup {x | ∃ sigma : ℝ, RefinedSigmaAdmissible theta eps sigma ∧
    x = min (ordinaryMomentExponent theta sigma)
      (additiveEnergyMomentExponent theta sigma)}

/-- The literal right side of Gafni--Tao Theorem 1.3, retaining the mandatory
infimum over every positive `epsilon`. -/
noncomputable def refinedExceptionalUpperExponent (theta : ℝ) : EReal :=
  sInf {x | ∃ eps : ℝ, 0 < eps ∧
    x = refinedFixedEpsilonExponent theta eps}

theorem refinedCandidate_le_fixedEpsilon
    {theta eps sigma : ℝ}
    (h : RefinedSigmaAdmissible theta eps sigma) :
    min (ordinaryMomentExponent theta sigma)
        (additiveEnergyMomentExponent theta sigma) ≤
      refinedFixedEpsilonExponent theta eps := by
  apply le_sSup
  exact ⟨sigma, h, rfl⟩

/-- Increasing the source epsilon weakens the density threshold and hence
can only enlarge the fixed-epsilon supremum.  This monotonicity is what lets
the final limit argument replace an arbitrary positive witness by a smaller
one for which the threshold remains positive. -/
theorem refinedFixedEpsilonExponent_mono
    {theta eps₁ eps₂ : ℝ} (heps : eps₁ ≤ eps₂) :
    refinedFixedEpsilonExponent theta eps₁ ≤
      refinedFixedEpsilonExponent theta eps₂ := by
  unfold refinedFixedEpsilonExponent
  apply sSup_le
  intro x hx
  rcases hx with ⟨sigma, hsigma, rfl⟩
  apply le_sSup
  refine ⟨sigma, ?_, rfl⟩
  refine ⟨hsigma.1, hsigma.2.1, ?_⟩
  have hthreshold :
      ((1 / (1 - theta) - eps₂ : ℝ) : EReal) ≤
        ((1 / (1 - theta) - eps₁ : ℝ) : EReal) := by
    exact_mod_cast
      (show 1 / (1 - theta) - eps₂ ≤
          1 / (1 - theta) - eps₁ by linarith)
  exact hthreshold.trans hsigma.2.2

theorem refinedFixedEpsilonExponent_eq_bot
    {theta eps : ℝ}
    (hEmpty : ∀ sigma : ℝ, ¬ RefinedSigmaAdmissible theta eps sigma) :
    refinedFixedEpsilonExponent theta eps = ⊥ := by
  rw [refinedFixedEpsilonExponent]
  apply sSup_eq_bot.mpr
  intro x hx
  rcases hx with ⟨sigma, hsigma, rfl⟩
  exact (hEmpty sigma hsigma).elim

theorem refinedExceptionalUpperExponent_le_fixedEpsilon
    {theta eps : ℝ} (heps : 0 < eps) :
    refinedExceptionalUpperExponent theta ≤
      refinedFixedEpsilonExponent theta eps := by
  apply sInf_le
  exact ⟨eps, heps, rfl⟩

/-- The exact source formula, exposed as an equality for downstream theorem
statements and audits. -/
theorem refinedExceptionalUpperExponent_eq_source_formula (theta : ℝ) :
    refinedExceptionalUpperExponent theta =
      sInf {x | ∃ eps : ℝ, 0 < eps ∧
        x = sSup {y | ∃ sigma : ℝ,
          (0 ≤ sigma ∧ sigma < 1 ∧
            ((1 / (1 - theta) - eps : ℝ) : EReal) ≤
              zeroDensityExponent sigma) ∧
          y = min
            ((((1 - theta) * (1 - sigma) : ℝ) : EReal) *
                zeroDensityExponent sigma + ((2 * sigma - 1 : ℝ) : EReal))
            ((((1 - theta) * (1 - sigma) : ℝ) : EReal) *
                zeroAdditiveEnergyExponent sigma +
                  ((4 * sigma - 3 : ℝ) : EReal))}} := by
  rfl

theorem zeroDensityExponent_ne_top_of_half_le
    {sigma : ℝ} (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1) :
    zeroDensityExponent sigma ≠ ⊤ := by
  intro htop
  have hle := zeroDensityExponent_le_thirty_thirteenths
    hsigmaLower hsigmaUpper
  rw [htop] at hle
  exact (not_le_of_gt (EReal.coe_lt_top (30 / 13 : ℝ))) hle

theorem zeroDensityExponent_ne_bot_of_coe_le
    {sigma lower : ℝ}
    (hlower : (lower : EReal) ≤ zeroDensityExponent sigma) :
    zeroDensityExponent sigma ≠ ⊥ := by
  intro hbot
  rw [hbot] at hlower
  exact (not_le_of_gt (EReal.bot_lt_coe lower)) hlower

theorem zeroAdditiveEnergyExponent_ne_top_of_half_le
    {sigma : ℝ} (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1) :
    zeroAdditiveEnergyExponent sigma ≠ ⊤ := by
  intro htop
  have hle := zeroAdditiveEnergyExponent_le_four_mul_of_zeroDensityEnvelope
    (frozen_uniform_thirty_thirteenths_zeroDensityEnvelope
      hsigmaLower hsigmaUpper)
  rw [htop] at hle
  exact (not_le_of_gt (EReal.coe_lt_top (4 * (30 / 13) : ℝ))) hle

theorem zeroAdditiveEnergyExponent_ne_bot_of_density_coe_le
    {sigma lower : ℝ}
    (hlower : (lower : EReal) ≤ zeroDensityExponent sigma) :
    zeroAdditiveEnergyExponent sigma ≠ ⊥ := by
  intro hbot
  have hle := zeroDensityExponent_le_zeroAdditiveEnergyExponent sigma
  rw [hbot] at hle
  exact zeroDensityExponent_ne_bot_of_coe_le hlower (bot_unique hle)

theorem ordinaryMomentExponent_eq_coe_toReal
    {theta sigma : ℝ}
    (htop : zeroDensityExponent sigma ≠ ⊤)
    (hbot : zeroDensityExponent sigma ≠ ⊥) :
    ordinaryMomentExponent theta sigma =
      (((1 - theta) * (1 - sigma) *
          (zeroDensityExponent sigma).toReal + 2 * sigma - 1 : ℝ) : EReal) := by
  calc
    ordinaryMomentExponent theta sigma =
        (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
          (((zeroDensityExponent sigma).toReal : ℝ) : EReal) +
            ((2 * sigma - 1 : ℝ) : EReal) := by
      rw [ordinaryMomentExponent, EReal.coe_toReal htop hbot]
    _ = (((1 - theta) * (1 - sigma) *
          (zeroDensityExponent sigma).toReal + 2 * sigma - 1 : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

theorem additiveEnergyMomentExponent_eq_coe_toReal
    {theta sigma : ℝ}
    (htop : zeroAdditiveEnergyExponent sigma ≠ ⊤)
    (hbot : zeroAdditiveEnergyExponent sigma ≠ ⊥) :
    additiveEnergyMomentExponent theta sigma =
      (((1 - theta) * (1 - sigma) *
          (zeroAdditiveEnergyExponent sigma).toReal +
            4 * sigma - 3 : ℝ) : EReal) := by
  calc
    additiveEnergyMomentExponent theta sigma =
        (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
          (((zeroAdditiveEnergyExponent sigma).toReal : ℝ) : EReal) +
            ((4 * sigma - 3 : ℝ) : EReal) := by
      rw [additiveEnergyMomentExponent, EReal.coe_toReal htop hbot]
    _ = (((1 - theta) * (1 - sigma) *
          (zeroAdditiveEnergyExponent sigma).toReal +
            4 * sigma - 3 : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

/-- A strict affine inequality survives replacement of a finite exponent by
a slightly larger real exponent.  This is the elementary epsilon margin used
to avoid any assumption that `A` or `A*` attains its defining infimum. -/
theorem exists_nonnegative_strict_upper_preserving_affine
    {c x r mu : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hlt : c * x + r < mu) :
    ∃ a : ℝ, 0 ≤ a ∧ x < a ∧ c * a + r ≤ mu := by
  let d := (mu - (c * x + r)) / (2 * c)
  have hd : 0 < d := div_pos (by linarith) (by positivity)
  refine ⟨x + d, by positivity, by linarith, ?_⟩
  have hcalc : c * (x + d) + r = ((c * x + r) + mu) / 2 := by
    dsimp [d]
    field_simp [hc.ne']
    ring
  rw [hcalc]
  linarith

/-- If the fixed-`epsilon` source supremum lies strictly below a real `mu`,
then every admissible sigma in the upper half of the critical strip admits
genuine finite envelope coefficients for which one of the two paper
alternatives is at most `mu`. -/
theorem exists_exponent_approximants_of_refinedFixedEpsilon_lt
    {theta eps sigma mu : ℝ}
    (htheta : theta < 1)
    (hthreshold : 0 < 1 / (1 - theta) - eps)
    (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma < 1)
    (hadmissible : RefinedSigmaAdmissible theta eps sigma)
    (hfixed : refinedFixedEpsilonExponent theta eps < (mu : EReal)) :
    ∃ aOrd aEnergy : ℝ,
      0 ≤ aOrd ∧ 0 ≤ aEnergy ∧
      zeroDensityExponent sigma < (aOrd : EReal) ∧
      zeroAdditiveEnergyExponent sigma < (aEnergy : EReal) ∧
      ((1 - theta) * (aOrd * (1 - sigma)) + 2 * sigma - 1 ≤ mu ∨
       (1 - theta) * (aEnergy * (1 - sigma)) + 4 * sigma - 3 ≤ mu) := by
  have hDensityLower := hadmissible.2.2
  have hSigmaUpperLe : sigma ≤ 1 := hsigmaUpper.le
  have hATop := zeroDensityExponent_ne_top_of_half_le
    hsigmaLower hSigmaUpperLe
  have hABot := zeroDensityExponent_ne_bot_of_coe_le hDensityLower
  have hETop := zeroAdditiveEnergyExponent_ne_top_of_half_le
    hsigmaLower hSigmaUpperLe
  have hEBot := zeroAdditiveEnergyExponent_ne_bot_of_density_coe_le hDensityLower
  have hCandidate :
      min (ordinaryMomentExponent theta sigma)
          (additiveEnergyMomentExponent theta sigma) < (mu : EReal) :=
    (refinedCandidate_le_fixedEpsilon hadmissible).trans_lt hfixed
  have hAUpper := zeroDensityExponent_le_thirty_thirteenths
    hsigmaLower hSigmaUpperLe
  have hEUpper := zeroAdditiveEnergyExponent_le_four_mul_of_zeroDensityEnvelope
    (frozen_uniform_thirty_thirteenths_zeroDensityEnvelope
      hsigmaLower hSigmaUpperLe)
  have hxA : 0 ≤ (zeroDensityExponent sigma).toReal := by
    have hreal := EReal.toReal_le_toReal hDensityLower
      (EReal.coe_ne_bot _) hATop
    simpa using hthreshold.le.trans hreal
  have hxE : 0 ≤ (zeroAdditiveEnergyExponent sigma).toReal := by
    have hAE := zeroDensityExponent_le_zeroAdditiveEnergyExponent sigma
    have hreal := EReal.toReal_le_toReal hAE hABot hETop
    exact hxA.trans hreal
  have hOrdUniversal :
      zeroDensityExponent sigma < ((30 / 13 + 1 : ℝ) : EReal) :=
    hAUpper.trans_lt (by exact_mod_cast (show (30 / 13 : ℝ) < 30 / 13 + 1 by linarith))
  have hEnergyUniversal :
      zeroAdditiveEnergyExponent sigma <
        ((4 * (30 / 13) + 1 : ℝ) : EReal) :=
    hEUpper.trans_lt (by
      exact_mod_cast
        (show (4 * (30 / 13) : ℝ) < 4 * (30 / 13) + 1 by linarith))
  rw [min_lt_iff] at hCandidate
  rcases hCandidate with hOrd | hEnergy
  · rw [ordinaryMomentExponent_eq_coe_toReal hATop hABot,
      EReal.coe_lt_coe_iff] at hOrd
    obtain ⟨aOrd, haOrd, hARealLt, hAlternative⟩ :=
      exists_nonnegative_strict_upper_preserving_affine
        (c := (1 - theta) * (1 - sigma))
        (x := (zeroDensityExponent sigma).toReal)
        (r := 2 * sigma - 1) (mu := mu)
        (mul_pos (by linarith) (by linarith)) hxA (by
          convert hOrd using 1
          all_goals ring_nf)
    refine ⟨aOrd, 4 * (30 / 13) + 1, haOrd, by norm_num,
      ?_, hEnergyUniversal, Or.inl ?_⟩
    · rw [← EReal.coe_toReal hATop hABot, EReal.coe_lt_coe_iff]
      exact hARealLt
    · convert hAlternative using 1
      all_goals ring_nf
  · rw [additiveEnergyMomentExponent_eq_coe_toReal hETop hEBot,
      EReal.coe_lt_coe_iff] at hEnergy
    obtain ⟨aEnergy, haEnergy, hERealLt, hAlternative⟩ :=
      exists_nonnegative_strict_upper_preserving_affine
        (c := (1 - theta) * (1 - sigma))
        (x := (zeroAdditiveEnergyExponent sigma).toReal)
        (r := 4 * sigma - 3) (mu := mu)
        (mul_pos (by linarith) (by linarith)) hxE
        (by
          convert hEnergy using 1
          all_goals ring_nf)
    refine ⟨30 / 13 + 1, aEnergy, by norm_num, haEnergy,
      hOrdUniversal, ?_, Or.inr ?_⟩
    · rw [← EReal.coe_toReal hETop hEBot, EReal.coe_lt_coe_iff]
      exact hERealLt
    · convert hAlternative using 1
      all_goals ring_nf

/-- Exact fixed-`epsilon` source consumer for one upper-half strip.  It starts
from membership in the literal supremum and ends at the literal
equation-(2.7) strip measure, deriving both analytic envelopes internally. -/
theorem equation27StripMeasure_epsilonBound_of_refinedFixedEpsilon_lt
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    {J j : ℕ} (hJ : 0 < J) (hj : j < J)
    {theta eps delta mu : ℝ}
    (htheta : theta < 1)
    (hthreshold : 0 < 1 / (1 - theta) - eps)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsigmaLower : 1 / 2 ≤ (j : ℝ) / J)
    (hadmissible :
      RefinedSigmaAdmissible theta eps ((j : ℝ) / J))
    (hfixed : refinedFixedEpsilonExponent theta eps < (mu : EReal)) :
    EpsilonExponentBound
      (fun X => equation27StripMeasure J j theta delta X)
      (mu + 4 / J) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsigmaUpper : (j : ℝ) / J < 1 := by
    rw [div_lt_one hJr]
    exact_mod_cast hj
  obtain ⟨aOrd, aEnergy, haOrd, haEnergy, hOrdExponent,
      hEnergyExponent, hAlternative⟩ :=
    exists_exponent_approximants_of_refinedFixedEpsilon_lt
      htheta hthreshold hsigmaLower hsigmaUpper hadmissible hfixed
  exact equation27StripMeasure_epsilonBound_of_exponent_upper_bounds cutoff
    hJ hj htheta hdelta hdeltaOne haOrd haEnergy hsigmaLower
      hOrdExponent hEnergyExponent hAlternative

/-- Every lower-half strip is controlled by the ordinary second moment with
the source baseline exponent `1-theta`, plus the literal `2/J` displacement
from the lower to the upper strip endpoint.  This includes the `j = 0` strip
and therefore removes the former artificial gap at the left edge. -/
theorem equation27StripMeasure_lowerHalf_epsilonBound
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    {J j : ℕ} (hJ : 0 < J) (hj : j < J)
    {theta delta : ℝ}
    (htheta : theta < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsigmaHalf : (j : ℝ) / J ≤ 1 / 2) :
    EpsilonExponentBound
      (fun X => equation27StripMeasure J j theta delta X)
      (1 - theta + 2 / J) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsigmaNonneg : 0 ≤ (j : ℝ) / J := by positivity
  have hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1 := by
    rw [div_le_one hJr]
    exact_mod_cast Nat.succ_le_iff.mpr hj
  have hDenom : 0 < 1 - (j : ℝ) / J := by linarith
  have ha : 0 ≤ 1 / (1 - (j : ℝ) / J) := by positivity
  have hDensity : ZeroDensityEnvelope ((j : ℝ) / J)
      (1 / (1 - (j : ℝ) / J)) :=
    lowerHalf_zeroDensityEnvelope hsigmaNonneg hsigmaHalf
  have hBound := equation27StripMeasure_second_epsilonBound cutoff
    hJ htheta hdelta hdeltaOne ha hsigmaNonneg hsigmaUpper hDensity
  apply hBound.mono_exponent
  have hSucc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_num
  rw [hSucc]
  have hCancel :
      (1 / (1 - (j : ℝ) / J)) * (1 - (j : ℝ) / J) = 1 := by
    exact one_div_mul_cancel hDenom.ne'
  rw [hCancel]
  have hStep : ((j : ℝ) + 1) / J = (j : ℝ) / J + 1 / J := by
    field_simp [hJr.ne']
  rw [hStep]
  have hsigmaTwice : 2 * ((j : ℝ) / J) ≤ 1 := by linarith
  ring_nf at hsigmaTwice ⊢
  linarith

/-- Finite equation-(2.7) assembly at fixed source epsilon.  The theorem
derives the lower-half, admissible refined, and small-`A` alternatives.  Its
only remaining strip input is the explicitly isolated fixed right-edge band,
which is where Lemma 2.1 and the Vinogradov--Korobov cutoff enter. -/
theorem equation27FullZeroMeasure_epsilonBound_of_refinedFixedEpsilon_lt
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    {J : ℕ} (hJ : 0 < J)
    {theta eps delta mu eta : ℝ}
    (htheta : theta < 1)
    (heps : 0 < eps)
    (hthreshold : 0 < 1 / (1 - theta) - eps)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hJMargin : 1 / (J : ℝ) < eps * (1 - theta) * eta)
    (hfixed : refinedFixedEpsilonExponent theta eps < (mu : EReal))
    (hRight : ∀ j ∈ Finset.range J,
      1 - eta < (j : ℝ) / J →
      EpsilonExponentBound
        (fun X => equation27StripMeasure J j theta delta X)
        (max (1 - theta) mu + 4 / J)) :
    EpsilonExponentBound
      (fun X => equation27FullZeroMeasure J theta delta X)
      (max (1 - theta) mu + 4 / J) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  apply equation27FullZeroMeasure_epsilonBound hJ hdelta
  intro j hj
  have hjLt : j < J := Finset.mem_range.mp hj
  have hsigmaNonneg : 0 ≤ (j : ℝ) / J := by positivity
  have hsigmaLtOne : (j : ℝ) / J < 1 := by
    rw [div_lt_one hJr]
    exact_mod_cast hjLt
  have hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1 := by
    rw [div_le_one hJr]
    exact_mod_cast Nat.succ_le_iff.mpr hjLt
  by_cases hLower : (j : ℝ) / J ≤ 1 / 2
  · have hBound := equation27StripMeasure_lowerHalf_epsilonBound cutoff
      hJ hjLt htheta hdelta hdeltaOne hLower
    apply hBound.mono_exponent
    have hTwoFour : (2 : ℝ) / J ≤ 4 / J :=
      (div_le_div_iff_of_pos_right hJr).2 (by norm_num)
    have hBase : 1 - theta ≤ max (1 - theta) mu := le_max_left _ _
    linarith
  · have hsigmaHalf : 1 / 2 ≤ (j : ℝ) / J := (lt_of_not_ge hLower).le
    by_cases hAtRight : 1 - eta < (j : ℝ) / J
    · exact hRight j hj hAtRight
    · have hInterior : (j : ℝ) / J ≤ 1 - eta := le_of_not_gt hAtRight
      by_cases hAdmissible :
          RefinedSigmaAdmissible theta eps ((j : ℝ) / J)
      · have hBound :=
          equation27StripMeasure_epsilonBound_of_refinedFixedEpsilon_lt
            cutoff hJ hjLt htheta hthreshold hdelta hdeltaOne hsigmaHalf
              hAdmissible hfixed
        apply hBound.mono_exponent
        linarith [le_max_right (1 - theta) mu]
      · have hANot : ¬(((1 / (1 - theta) - eps : ℝ) : EReal) ≤
            zeroDensityExponent ((j : ℝ) / J)) := by
          intro hA
          exact hAdmissible ⟨hsigmaNonneg, hsigmaLtOne, hA⟩
        have hA : zeroDensityExponent ((j : ℝ) / J) <
            (((1 / (1 - theta) - eps : ℝ) : EReal)) :=
          lt_of_not_ge hANot
        have hsigmaPos : 0 < (j : ℝ) / J :=
          lt_of_lt_of_le (by norm_num) hsigmaHalf
        have hGap : 0 < 1 - theta := by linarith
        have hInteriorGap : eta ≤ 1 - (j : ℝ) / J := by linarith
        have hMargin : 1 / (J : ℝ) <
            eps * (1 - theta) * (1 - (j : ℝ) / J) := by
          have hCoeff : 0 < eps * (1 - theta) := by
            exact mul_pos heps hGap
          exact hJMargin.trans_le
            (mul_le_mul_of_nonneg_left hInteriorGap hCoeff.le)
        have hEmpty := eventually_equation27StripLargeSet_eq_empty_of_small_A
          hJ htheta hdelta hdeltaOne hthreshold.le hsigmaPos hsigmaUpper
            hA hMargin
        exact equation27StripMeasure_epsilonBound_of_eventually_empty hEmpty

end GafniTao

import GafniTao.PintzFiniteEnvelope
import GafniTao.FordAsymptoticZeroFree

/-!
# The unconditional near-one logarithmic density input

The source range is split exactly as follows.

* Below the Vinogradov--Korobov boundary the count vanishes.
* Up to `eta = 1/8` the corrected Pintz detector supplies the exponent
  `8 L eta^(3/2)` and 523 logarithmic powers.
* From `eta = 1/8` to `eta = 1/2`, the uniform full-strip Jensen estimate is
  absorbed by the much larger Pintz exponent.

One additional logarithmic power absorbs all fixed coefficients.
-/

open Asymptotics Filter

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintzNearOneDensityCoefficient : ℝ :=
  8 * pintzDensityLambdaCoefficient

theorem pintzNearOneDensityCoefficient_pos :
    0 < pintzNearOneDensityCoefficient := by
  unfold pintzNearOneDensityCoefficient
  exact mul_pos (by norm_num) pintzDensityLambdaCoefficient_pos

theorem two_le_pintzNearOne_exponent_of_one_eighth_lt
    {eta : ℝ} (heta : 1 / 8 < eta) (hetaUpper : eta ≤ 1 / 2) :
    2 ≤ pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ) := by
  have hetaPos : 0 < eta := by linarith
  have hetaOne : eta ≤ 1 := by linarith
  have hsquare : eta ^ 2 ≤ eta := by nlinarith
  have hsqrt : eta ≤ Real.sqrt eta := by
    rw [Real.le_sqrt hetaPos.le]
    · nlinarith
    · exact hetaPos.le
  have hetaPow : eta ^ 2 ≤ eta ^ (3 / 2 : ℝ) := by
    rw [eta_three_halves_eq_eta_mul_sqrt hetaPos.le]
    nlinarith
  have hL : 1280 ≤ pintzDensityLambdaCoefficient := by
    unfold pintzDensityLambdaCoefficient
    nlinarith [four_le_fordSourceB_three_million]
  unfold pintzNearOneDensityCoefficient
  nlinarith [sq_nonneg (eta - 1 / 8)]

theorem zeroCount_anti_sigma_native
    {sigmaLower sigmaUpper T : ℝ} (hSigma : sigmaLower ≤ sigmaUpper) :
    zeroCount sigmaUpper T ≤ zeroCount sigmaLower T := by
  unfold zeroCount N
  exact zeroCountRect_mono sigmaUpper 1 (-T) T sigmaLower 1 (-T) T
    hSigma le_rfl le_rfl le_rfl

/-- Pintz's near-one density estimate, with the implied coefficient absorbed
into the 524th logarithmic power.  Both constants are explicit; only the
lower height is existential, as in the published asymptotic statement. -/
theorem exists_pintz_nearOne_log_density_native :
    ∃ c Tzero Tdensity : ℝ,
      0 < c ∧
      VinogradovKorobovCountVanishing c Tzero ∧
      NearOneLogDensityBound pintzNearOneDensityCoefficient 524 Tdensity := by
  obtain ⟨c₀, H₀, hc₀, hH₀, hPointwise⟩ :=
    ford_asymptotic_zero_free_native
  obtain ⟨c, hc, _hcLe, hRectangle⟩ :=
    exists_vinogradovKorobovRectangleZeroFree_of_pointwise
      hc₀ hH₀ hPointwise
  have hZeroFree : VinogradovKorobovCountVanishing c H₀ :=
    vinogradovKorobovCountVanishing_of_rectangleZeroFree hRectangle
  have hLambdaEventual := eventually_two_pintzDensityLambda_le_height hc
  rw [eventually_atTop] at hLambdaEventual
  obtain ⟨Hlambda, hLambda⟩ := hLambdaEventual
  have hGlobalO := global_zero_count_epsilon_one (1 / 2) (by norm_num)
    1 zero_lt_one
  obtain ⟨Kglobal, hGlobal⟩ := hGlobalO.bound
  rw [eventually_atTop] at hGlobal
  obtain ⟨Hglobal, hGlobal⟩ := hGlobal
  let K : ℝ := max (pintzNativeEnvelopeCoefficient c) (max Kglobal 1)
  let Tdensity : ℝ :=
    max H₀ (max Hlambda (max Hglobal
      (max (max (Real.exp 2) 8)
        (max (pintzContourErrorHeight c)
          (max (pintzCoreAbsorptionHeight c) (Real.exp K))))))
  refine ⟨c, H₀, Tdensity, hc, hZeroFree, ?_⟩
  intro eta T heta hetaUpper hT
  have hH₀T : H₀ ≤ T := (le_max_left _ _).trans hT
  have hAfterZero :
      max Hlambda (max Hglobal
        (max (max (Real.exp 2) 8)
          (max (pintzContourErrorHeight c)
            (max (pintzCoreAbsorptionHeight c) (Real.exp K))))) ≤ T :=
    (le_max_right H₀ _).trans hT
  have hHlambdaT : Hlambda ≤ T := (le_max_left _ _).trans hAfterZero
  have hAfterLambda :
      max Hglobal
        (max (max (Real.exp 2) 8)
          (max (pintzContourErrorHeight c)
            (max (pintzCoreAbsorptionHeight c) (Real.exp K)))) ≤ T :=
    (le_max_right Hlambda _).trans hAfterZero
  have hHglobalT : Hglobal ≤ T := (le_max_left _ _).trans hAfterLambda
  have hAfterGlobal :
      max (max (Real.exp 2) 8)
        (max (pintzContourErrorHeight c)
          (max (pintzCoreAbsorptionHeight c) (Real.exp K))) ≤ T :=
    (le_max_right Hglobal _).trans hAfterLambda
  have hBasic : max (Real.exp 2) 8 ≤ T :=
    (le_max_left _ _).trans hAfterGlobal
  have hAfterBasic :
      max (pintzContourErrorHeight c)
        (max (pintzCoreAbsorptionHeight c) (Real.exp K)) ≤ T :=
    (le_max_right (max (Real.exp 2) 8) _).trans hAfterGlobal
  have hError : pintzContourErrorHeight c ≤ T :=
    (le_max_left _ _).trans hAfterBasic
  have hAfterError :
      max (pintzCoreAbsorptionHeight c) (Real.exp K) ≤ T :=
    (le_max_right (pintzContourErrorHeight c) _).trans hAfterBasic
  have hCore : pintzCoreAbsorptionHeight c ≤ T :=
    (le_max_left _ _).trans hAfterError
  have hExpK : Real.exp K ≤ T :=
    (le_max_right _ _).trans hAfterError
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hExpK
  have hTone : 1 ≤ T := by
    have hEight : (8 : ℝ) ≤ T := (le_max_right (Real.exp 2) 8).trans hBasic
    linarith
  have hlogK : K ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos K) hTpos hExpK
  have hlogOne : 1 ≤ Real.log T :=
    (le_max_right Kglobal 1 |>.trans (le_max_right
      (pintzNativeEnvelopeCoefficient c) (max Kglobal 1))).trans hlogK
  have hlogPos : 0 < Real.log T := zero_lt_one.trans_le hlogOne
  have hlogSplit :
      Real.log T * Real.log T ^ (523 : ℝ) =
        Real.log T ^ (524 : ℝ) := by
    calc
      _ = Real.log T ^ (1 : ℝ) * Real.log T ^ (523 : ℝ) := by
        rw [Real.rpow_one]
      _ = _ := (Real.rpow_add hlogPos 1 523).symm.trans (by norm_num)
  by_cases hetaVK : eta ≤ c / vinogradovKorobovDenominator T
  · have hzero := hZeroFree heta hH₀T hetaVK
    rw [hzero]
    norm_num
    exact mul_nonneg
      (Real.rpow_nonneg hTpos.le
        (pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ)))
      (pow_nonneg hlogPos.le 524)
  have hetaAbove : c / vinogradovKorobovDenominator T < eta :=
    lt_of_not_ge hetaVK
  by_cases hetaSmall : eta ≤ 1 / 8
  · have hLambdaHeight := hLambda T hHlambdaT eta heta (by linarith) hetaAbove
    have hNative := pintz_zeroCount_native_envelope hc heta hetaSmall hBasic
      hError hCore hLambdaHeight hetaAbove
    have hKNative : pintzNativeEnvelopeCoefficient c ≤ Real.log T :=
      (le_max_left _ _).trans hlogK
    calc
      (zeroCount (1 - eta) T : ℝ) ≤
          pintzNativeEnvelopeCoefficient c *
            T ^ (pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ)) *
            Real.log T ^ (523 : ℝ) := by
        simpa [pintzNearOneDensityCoefficient] using hNative
      _ ≤ T ^ (pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ)) *
          (Real.log T * Real.log T ^ (523 : ℝ)) := by
        have hPower : 0 ≤ T ^
            (pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ)) :=
          Real.rpow_nonneg hTpos.le _
        have hLogPower : 0 ≤ Real.log T ^ (523 : ℝ) :=
          Real.rpow_nonneg hlogPos.le _
        nlinarith [mul_nonneg (sub_nonneg.mpr hKNative)
          (mul_nonneg hPower hLogPower)]
      _ = _ := by rw [hlogSplit]
  · have hetaLarge : 1 / 8 < eta := lt_of_not_ge hetaSmall
    have hExponent :=
      two_le_pintzNearOne_exponent_of_one_eighth_lt hetaLarge hetaUpper
    have hHalfSubset : zeroCount (1 - eta) T ≤ zeroCount (1 / 2) T :=
      zeroCount_anti_sigma_native (by linarith)
    have hGlobalRaw := hGlobal T hHglobalT
    have hGlobalBound : (zeroCount (1 / 2) T : ℝ) ≤
        Kglobal * T ^ (2 : ℝ) := by
      have hCountNonneg : 0 ≤ (zeroCount (1 / 2) T : ℝ) := by positivity
      have hRightNonneg : 0 ≤ T ^ (1 : ℝ) * |T ^ (1 : ℝ)| := by positivity
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hCountNonneg,
        Real.norm_eq_abs, abs_of_nonneg hRightNonneg,
        Real.rpow_one, abs_of_nonneg hTpos.le] at hGlobalRaw
      simpa [Real.rpow_two, pow_two] using hGlobalRaw
    have hKGlobal : Kglobal ≤ Real.log T :=
      (le_max_left Kglobal 1 |>.trans
        (le_max_right (pintzNativeEnvelopeCoefficient c) _)).trans hlogK
    have hPowerMono : T ^ (2 : ℝ) ≤
        T ^ (pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hTone hExponent
    have hCountReal : (zeroCount (1 - eta) T : ℝ) ≤
        (zeroCount (1 / 2) T : ℝ) := by exact_mod_cast hHalfSubset
    calc
      (zeroCount (1 - eta) T : ℝ) ≤ (zeroCount (1 / 2) T : ℝ) := hCountReal
      _ ≤ Kglobal * T ^ (2 : ℝ) := hGlobalBound
      _ ≤ Real.log T *
          T ^ (pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ)) := by
        have hTtwo : 0 ≤ T ^ (2 : ℝ) := Real.rpow_nonneg hTpos.le _
        calc
          Kglobal * T ^ (2 : ℝ) ≤ Real.log T * T ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_right hKGlobal hTtwo
          _ ≤ Real.log T *
              T ^ (pintzNearOneDensityCoefficient *
                eta ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hPowerMono
              (zero_le_one.trans hlogOne)
      _ ≤ T ^ (pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ)) *
          (Real.log T * Real.log T ^ (523 : ℝ)) := by
        have hPower : 0 ≤ T ^
            (pintzNearOneDensityCoefficient * eta ^ (3 / 2 : ℝ)) :=
          Real.rpow_nonneg hTpos.le _
        nlinarith [mul_nonneg (mul_nonneg hPower (zero_le_one.trans hlogOne))
          (sub_nonneg.mpr (Real.one_le_rpow hlogOne (by norm_num :
            (0 : ℝ) ≤ 523)))]
      _ = _ := by rw [hlogSplit]

#print axioms two_le_pintzNearOne_exponent_of_one_eighth_lt
#print axioms zeroCount_anti_sigma_native
#print axioms exists_pintz_nearOne_log_density_native

end

end GafniTao

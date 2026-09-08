import GafniTao.PintzNearOneNative
import GafniTao.RefinedEnvelope

/-!
# Near-one logarithmic density as an ordinary density exponent

This module converts the literal Pintz logarithmic estimate into the
epsilon-power normalization used by `A(sigma)`.  The logarithm is absorbed
only here, after its source-faithful form has already been proved.
-/

open Asymptotics Filter

namespace GafniTao

/-- A `T^(C eta^(3/2)) log(T)^B` count yields the source-normalized
coefficient `C sqrt(eta)` at `sigma = 1-eta`. -/
theorem nearOneLogDensityBound_zeroDensityEnvelope
    {C B Tzero eta : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 2) :
    ZeroDensityEnvelope (1 - eta) (C * eta ^ (1 / 2 : ℝ)) := by
  unfold ZeroDensityEnvelope EpsilonExponentBound
  intro eps heps
  have hlogLittle :
      (fun T : ℝ => Real.log T ^ B) =o[atTop] (fun T => T ^ eps) :=
    isLittleO_log_rpow_rpow_atTop B heps
  obtain ⟨K, _hKpos, hK⟩ := hlogLittle.isBigO.exists_pos
  have hcount : ∀ᶠ T : ℝ in atTop,
      |(zeroCount (1 - eta) T : ℝ)| ≤
        T ^ (C * eta ^ (3 / 2 : ℝ)) * |Real.log T ^ B| := by
    filter_upwards [eventually_ge_atTop Tzero, eventually_ge_atTop 1]
      with T hT hTone
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      (zeroCount (1 - eta) T : ℝ) ≤
          T ^ (C * eta ^ (3 / 2 : ℝ)) * Real.log T ^ B :=
        hDensity heta hetaUpper hT
      _ ≤ T ^ (C * eta ^ (3 / 2 : ℝ)) *
          |Real.log T ^ B| := by
        gcongr
        exact le_abs_self _
  refine IsBigO.of_bound K ?_
  filter_upwards [hcount, hK.bound, eventually_ge_atTop 1]
    with T hcountT hlogT hTone
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hpowNonneg : 0 ≤ T ^ (C * eta ^ (3 / 2 : ℝ)) :=
    Real.rpow_nonneg hTpos.le _
  have hexp : C * eta ^ (3 / 2 : ℝ) =
      (C * eta ^ (1 / 2 : ℝ)) * (1 - (1 - eta)) := by
    rw [eta_three_halves_eq_mul_sqrt heta.le]
    ring
  calc
    ‖|(zeroCount (1 - eta) T : ℝ)|‖ =
        |(zeroCount (1 - eta) T : ℝ)| := by simp
    _ ≤
        T ^ (C * eta ^ (3 / 2 : ℝ)) * |Real.log T ^ B| := hcountT
    _ ≤ T ^ (C * eta ^ (3 / 2 : ℝ)) * (K * |T ^ eps|) := by
      gcongr
      simpa only [Real.norm_eq_abs] using hlogT
    _ = K * (T ^ eps *
        |T ^ ((C * eta ^ (1 / 2 : ℝ)) * (1 - (1 - eta)))|) := by
      rw [abs_of_nonneg (Real.rpow_nonneg hTpos.le _),
        abs_of_nonneg (Real.rpow_nonneg hTpos.le _), ← hexp]
      ring
    _ = K * ‖T ^ eps *
        |T ^ ((C * eta ^ (1 / 2 : ℝ)) * (1 - (1 - eta)))|‖ := by
      simp only [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hTpos.le _)]

/-- Count-level Pintz consequence for the actual least exponent `A`. -/
theorem zeroDensityExponent_le_nearOne
    {C B Tzero eta : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 2) :
    zeroDensityExponent (1 - eta) ≤
      ((C * eta ^ (1 / 2 : ℝ) : ℝ) : EReal) :=
  zeroDensityExponent_le
    (nearOneLogDensityBound_zeroDensityEnvelope hDensity heta hetaUpper)

/-- Pintz's logarithmic density estimate forces every upper-half admissible
point a definite distance from the right edge.  The lower bound is kept in
the exact squared form needed by the subsequent uniform-density exponent
calculation. -/
theorem one_sub_sigma_lower_of_upperHalf_admissible
    {C B Tzero theta eps sigma : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hC : 0 < C)
    (hthreshold : 0 < 1 / (1 - theta) - eps)
    (hsigma : UpperHalfRefinedSigmaAdmissible theta eps sigma) :
    ((1 / (1 - theta) - eps) / C) ^ 2 ≤ 1 - sigma := by
  let eta : ℝ := 1 - sigma
  have heta : 0 < eta := by
    dsimp only [eta]
    linarith [hsigma.2.1]
  have hetaUpper : eta ≤ 1 / 2 := by
    dsimp only [eta]
    linarith [hsigma.1]
  have hExponent : zeroDensityExponent sigma ≤
      ((C * eta ^ (1 / 2 : ℝ) : ℝ) : EReal) := by
    simpa only [eta, sub_sub_cancel] using
      (zeroDensityExponent_le_nearOne hDensity heta hetaUpper)
  have hCoe : ((1 / (1 - theta) - eps : ℝ) : EReal) ≤
      ((C * eta ^ (1 / 2 : ℝ) : ℝ) : EReal) :=
    hsigma.2.2.trans hExponent
  have hReal : 1 / (1 - theta) - eps ≤
      C * eta ^ (1 / 2 : ℝ) := by
    exact_mod_cast hCoe
  have hDiv : (1 / (1 - theta) - eps) / C ≤
      eta ^ (1 / 2 : ℝ) := (div_le_iff₀ hC).2 (by
        simpa only [mul_comm] using hReal)
  have hDivNonneg : 0 ≤ (1 / (1 - theta) - eps) / C :=
    div_nonneg hthreshold.le hC.le
  have hSq : ((1 / (1 - theta) - eps) / C) ^ 2 ≤
      (eta ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hDivNonneg hDiv 2
  calc
    ((1 / (1 - theta) - eps) / C) ^ 2 ≤
        (eta ^ (1 / 2 : ℝ)) ^ 2 := hSq
    _ = eta := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt heta.le]
    _ = 1 - sigma := rfl

end GafniTao

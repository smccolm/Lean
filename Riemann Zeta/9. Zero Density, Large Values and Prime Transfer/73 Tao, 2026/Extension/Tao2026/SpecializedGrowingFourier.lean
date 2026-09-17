import Tao2026.FourierDecayRate
import Tao2026.SpecializedFourierReconstruction

/-!
# Polylogarithmically growing Fourier boxes

This module chooses an explicit logarithmic Fourier radius and combines it
with the quantitative radial tail estimate.  It also records the exponent
margin that lets every retained frequency remain inside the stretched-log
Vinogradov parameter range.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace Tao2026

noncomputable section

/-- The Fourier radius obtained by rounding up a fixed integral power of
`log P`. -/
def specializedFourierRadius (B P : ℕ) : ℕ :=
  ⌈(Real.log P) ^ B⌉₊

theorem log_pow_le_specializedFourierRadius (B P : ℕ) :
    (Real.log P) ^ B ≤ (specializedFourierRadius B P : ℝ) := by
  exact Nat.le_ceil _

theorem specializedFourierRadius_lt_log_pow_add_one
    {B P : ℕ} (hlog : 0 ≤ Real.log P) :
    (specializedFourierRadius B P : ℝ) < (Real.log P) ^ B + 1 := by
  exact Nat.ceil_lt_add_one (pow_nonneg hlog B)

/-- The universal cubic radial tail at logarithmic radius `2T` has the
explicit inverse-logarithmic bound required for Fourier reconstruction. -/
theorem fourierDecayTail_specializedFourierRadius_le
    (T : ℕ) {P : ℕ} (hP : 2 ≤ P) :
    (∑' q : {q // q ∉ fourierFrequencyBox
        (specializedFourierRadius (2 * T) P)}, fourierDecayWeight q) ≤
      (Real.log P) ^ (-(T : ℝ)) *
        ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q := by
  have hlog : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hradius := fourierDecayTail_le_invSqrt
    (specializedFourierRadius (2 * T) P)
  have hlower : (Real.log P) ^ (2 * T) ≤
      (specializedFourierRadius (2 * T) P : ℝ) + 1 := by
    exact (log_pow_le_specializedFourierRadius (2 * T) P).trans
      (by linarith)
  have hfactor :
      ((specializedFourierRadius (2 * T) P : ℝ) + 1) ^
          (-(1 / 2 : ℝ)) ≤
        (Real.log P) ^ (-(T : ℝ)) := by
    have hpowpos : 0 < (Real.log P) ^ (2 * T) := pow_pos hlog _
    have hmono := Real.rpow_le_rpow_of_nonpos hpowpos hlower
      (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    refine hmono.trans_eq ?_
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hlog.le]
    congr 1
    push_cast
    ring
  exact hradius.trans (mul_le_mul_of_nonneg_right hfactor
    (tsum_nonneg fourierDecayWeightFiveHalves_nonneg))

/-- A fixed power of `log P` can be inserted into a stretched exponential
after increasing its positive logarithmic exponent. -/
theorem eventually_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
    {α β : ℝ} (hβ : 0 < β) (hαβ : α < β) (B : ℕ) :
    ∀ᶠ P : ℕ in atTop,
      (Real.log P) ^ (B : ℝ) * Real.exp ((Real.log P) ^ α) ≤
        Real.exp ((Real.log P) ^ β) := by
  have hratio : Tendsto
      (fun P : ℕ => (Real.log P) ^ (-(β - α))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hαβ)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hratioHalf : ∀ᶠ P : ℕ in atTop,
      (Real.log P) ^ (-(β - α)) ≤ (1 / 2 : ℝ) :=
    hratio.eventually (Iic_mem_nhds (by norm_num))
  have habsorbReal :=
    eventually_log_rpow_mul_exp_neg_log_rpow_le_log_rpow_neg
      (A := (0 : ℝ)) (b := (B : ℝ))
      (by norm_num : (0 : ℝ) < 1 / 2) hβ
  have habsorb : ∀ᶠ P : ℕ in atTop,
      (Real.log P) ^ (B : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * (Real.log P) ^ β) ≤ 1 := by
    have hcomp := tendsto_natCast_atTop_atTop.eventually habsorbReal
    filter_upwards [hcomp] with P hP
    norm_num at hP ⊢
    exact hP
  filter_upwards [hratioHalf, habsorb, eventually_ge_atTop (2 : ℕ)] with
      P hratioP habsorbP hP
  have hlog : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hpower : (Real.log P) ^ α ≤
      (1 / 2 : ℝ) * (Real.log P) ^ β := by
    calc
      (Real.log P) ^ α =
          (Real.log P) ^ β * (Real.log P) ^ (-(β - α)) := by
        rw [← Real.rpow_add hlog]
        congr 1
        ring
      _ ≤ (Real.log P) ^ β * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hratioP (Real.rpow_nonneg hlog.le _)
      _ = (1 / 2 : ℝ) * (Real.log P) ^ β := by ring
  have hexp : Real.exp ((Real.log P) ^ α - (Real.log P) ^ β) ≤
      Real.exp (-(1 / 2 : ℝ) * (Real.log P) ^ β) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    (Real.log P) ^ (B : ℝ) * Real.exp ((Real.log P) ^ α) =
        ((Real.log P) ^ (B : ℝ) *
            Real.exp ((Real.log P) ^ α - (Real.log P) ^ β)) *
          Real.exp ((Real.log P) ^ β) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ ((Real.log P) ^ (B : ℝ) *
            Real.exp (-(1 / 2 : ℝ) * (Real.log P) ^ β)) *
          Real.exp ((Real.log P) ^ β) := by
      gcongr
    _ ≤ 1 * Real.exp ((Real.log P) ^ β) := by
      gcongr
    _ = Real.exp ((Real.log P) ^ β) := one_mul _

/-- Membership in a polylogarithmically growing Fourier box spends half of
the positive stretched-log margin and restores a fixed Vinogradov constant. -/
theorem eventually_vinogradovParameterBounds_of_mem_specializedFourierBox
    (B : ℕ) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ P : ℕ in atTop, ∀ (q : ℤ × ℤ) (N : ℝ),
      q ∈ fourierFrequencyBox (specializedFourierRadius B P) →
      VinogradovParameterBound ε K P N →
      VinogradovParameterBound (ε / 2) (3 * K) P ((q.1 : ℝ) * N) ∧
        VinogradovParameterBound (ε / 2) (3 * K) P ((q.2 : ℝ) * N) := by
  have hβ : 0 < 3 / 2 - ε / 2 := by linarith
  have hαβ : 3 / 2 - ε < 3 / 2 - ε / 2 := by linarith
  have hstretch :=
    eventually_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      hβ hαβ B
  have hlogOne : ∀ᶠ P : ℕ in atTop, 1 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hstretch, hlogOne] with P hstretchP hlogP
  intro q N hq hN
  have hlogNonneg : 0 ≤ Real.log (P : ℝ) := zero_le_one.trans hlogP
  have hpowOne : 1 ≤ (Real.log P) ^ (B : ℝ) :=
    Real.one_le_rpow hlogP (Nat.cast_nonneg B)
  have hradius := specializedFourierRadius_lt_log_pow_add_one
    (B := B) (P := P) hlogNonneg
  have hpowEq : (Real.log P) ^ B = (Real.log P) ^ (B : ℝ) :=
    (Real.rpow_natCast _ _).symm
  have hradiusBound :
      (specializedFourierRadius B P : ℝ) + 1 ≤
        3 * (Real.log P) ^ (B : ℝ) := by
    rw [hpowEq] at hradius
    linarith
  have hparams := vinogradovParameterBounds_of_mem_fourierFrequencyBox
    hN hN hq
  constructor
  · change |(q.1 : ℝ) * N| ≤
      (3 * K) * Real.exp ((Real.log P) ^ (3 / 2 - ε / 2))
    calc
      |(q.1 : ℝ) * N| ≤
          (((specializedFourierRadius B P : ℝ) + 1) * K) *
            Real.exp ((Real.log P) ^ (3 / 2 - ε)) := hparams.1
      _ ≤ (3 * (Real.log P) ^ (B : ℝ) * K) *
            Real.exp ((Real.log P) ^ (3 / 2 - ε)) := by
        gcongr
      _ = (3 * K) * ((Real.log P) ^ (B : ℝ) *
            Real.exp ((Real.log P) ^ (3 / 2 - ε))) := by ring
      _ ≤ (3 * K) * Real.exp ((Real.log P) ^ (3 / 2 - ε / 2)) := by
        gcongr
  · change |(q.2 : ℝ) * N| ≤
      (3 * K) * Real.exp ((Real.log P) ^ (3 / 2 - ε / 2))
    calc
      |(q.2 : ℝ) * N| ≤
          (((specializedFourierRadius B P : ℝ) + 1) * K) *
            Real.exp ((Real.log P) ^ (3 / 2 - ε)) := hparams.2
      _ ≤ (3 * (Real.log P) ^ (B : ℝ) * K) *
            Real.exp ((Real.log P) ^ (3 / 2 - ε)) := by
        gcongr
      _ = (3 * K) * ((Real.log P) ^ (B : ℝ) *
            Real.exp ((Real.log P) ^ (3 / 2 - ε))) := by ring
      _ ≤ (3 * K) * Real.exp ((Real.log P) ^ (3 / 2 - ε / 2)) := by
        gcongr

/-- Radius-free specialized mode partition.  The high-frequency source
theorems only need fixed coefficient bounds; the sole retained-frequency
geometry used by the opposite-sign chamber is `4 |q₂| ≤ P`. -/
theorem eventually_specializedFourierMode_Ico_le_highLowMajorant_of_phaseBounds
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      4 * |(q.2 : ℝ)| ≤ (P : ℝ) →
      |(q.1 : ℝ) * N| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      |(q.2 : ℝ) * N| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N N 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N N 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S +
          vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S : ℝ)) +
          20 * (P : ℝ) /
            ((Real.log b) ^
                vaughanTypeIILogSavingPhaseExponent ((S : ℝ) + 1) *
              Real.log P) := by
  let Sℝ : ℝ := S
  let d : ℝ := vaughanTypeIILogSavingPhaseExponent (Sℝ + 1)
  obtain ⟨D, hsplit⟩ :=
    exists_eventually_reciprocalPhaseScale_low_or_log_rpow_high d
  obtain ⟨C, hC, hlow⟩ :=
    hPNT.eventually_primeFourierMode_sub_integral_Ico_le_logSaving D S
  have hsame :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_sameSign_sourceScale
      hVinogradov hA₀ hε haexp (Nat.cast_nonneg S)
  have hstationary :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_stationary_left
      hVinogradov hA₀ hε haexp (Nat.cast_nonneg S)
  have hzeroLinear :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_zero_linear
      hVinogradov hA₀ hε haexp (Nat.cast_nonneg S)
  have hzeroQuadratic :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_zero_quadratic
      hVinogradov hA₀ hε haexp (Nat.cast_nonneg S)
  have hlogTwo : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hsplit, hlow, hsame, hstationary, hzeroLinear,
    hzeroQuadratic, hlogTwo] with
      P hsplitP hlowP hsameP hstationaryP hzeroLinearP hzeroQuadraticP
      hlogP
  intro a b q N hPa hab hbP hqGeometry hNupper hMupper
  have hP2 : 2 ≤ P := by
    have hlogPpos : 0 < Real.log (P : ℝ) := by linarith
    have hPone : (1 : ℝ) < P := (Real.log_pos_iff (by positivity)).mp hlogPpos
    have hPoneNat : 1 < P := by exact_mod_cast hPone
    omega
  have hPpos : 0 < (P : ℝ) := by positivity
  have hPb : P ≤ b := hPa.trans hab.le
  have hlogPpos : 0 < Real.log (P : ℝ) := by linarith
  have hlogbpos : 0 < Real.log (b : ℝ) := by
    exact hlogPpos.trans_le
      (Real.log_le_log hPpos (by exact_mod_cast hPb))
  let H : ℝ := (Real.log b) ^ d
  have hHpos : 0 < H := by
    dsimp only [H]
    exact Real.rpow_pos_of_pos hlogbpos d
  have hlogbTwo : 2 ≤ Real.log (b : ℝ) :=
    hlogP.trans (Real.log_le_log hPpos (by exact_mod_cast hPb))
  have hdTwo : (2 : ℝ) ≤ d := by
    dsimp only [d, Sℝ, vaughanTypeIILogSavingPhaseExponent]
    have hScast : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    nlinarith
  have hHfour : 4 ≤ H := by
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ Real.log (b : ℝ)) hdTwo
    rw [Real.rpow_two] at hpow
    dsimp only [H]
    nlinarith [sq_nonneg (Real.log (b : ℝ) - 2)]
  have hlowTerm : 0 ≤ (P : ℝ) / (Real.log P) ^ S := by positivity
  have hprimeTerm : 0 ≤
      vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
        (Real.log P) ^ (-(S : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg vaughanPrimeQuadraticDecayConstant_pos.le (by positivity))
      (Real.rpow_nonneg hlogPpos.le _)
  have hintegralTerm : 0 ≤ (P : ℝ) / (H * Real.log P) := by positivity
  rcases hsplitP b ((q.1 : ℝ) * N) ((q.2 : ℝ) * N) hPb hbP with
      hlowScale | hhighScale
  · have hbound := hlowP a b q N N hPa hab hbP hlowScale
    have hmajorIntegral : 0 ≤
        20 * (P : ℝ) / (H * Real.log P) := by positivity
    dsimp only [Sℝ, d, H] at *
    linarith
  · have hlogLower : (Real.log b) ^
        vaughanTypeIILogSavingPhaseExponent ((S : ℝ) + 1) ≤ H := by
      rfl
    have hhighScale' : H ≤ reciprocalPhaseScale
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * N) 2 (4 * (P : ℝ)) := by
      simpa only [H, d, Sℝ] using hhighScale
    by_cases hA : (q.1 : ℝ) * N = 0
    · by_cases hB : (q.2 : ℝ) * N = 0
      · have hzero : H ≤ 0 := by
          simpa [hA, hB, reciprocalPhaseScale] using hhighScale'
        exact (not_lt_of_ge hzero hHpos).elim
      · have hbound := hzeroLinearP a b q N N H hPa hab hbP
          hA hB hHpos hlogLower hhighScale' hNupper hMupper
        have hcoeff : (P : ℝ) / (H * Real.log P) ≤
            20 * (P : ℝ) / (H * Real.log P) := by
          apply (div_le_div_iff_of_pos_right (mul_pos hHpos hlogPpos)).2
          nlinarith
        dsimp only [Sℝ, d, H] at *
        linarith
    · by_cases hB : (q.2 : ℝ) * N = 0
      · have hbound := hzeroQuadraticP a b q N N H hPa hab hbP
          hA hB hHpos hlogLower hhighScale' hNupper
        have hcoeff : 2 * (P : ℝ) / (H * Real.log P) ≤
            20 * (P : ℝ) / (H * Real.log P) := by
          apply (div_le_div_iff_of_pos_right (mul_pos hHpos hlogPpos)).2
          nlinarith
        dsimp only [Sℝ, d, H] at *
        linarith
      · by_cases hsign :
          (0 < (q.1 : ℝ) * N ∧ 0 < (q.2 : ℝ) * N) ∨
            ((q.1 : ℝ) * N < 0 ∧ (q.2 : ℝ) * N < 0)
        · have hbound := hsameP a b q N N H hPa hab hbP hsign hHpos
            hlogLower hhighScale' hNupper hMupper
          have hcoeff : 6 * (P : ℝ) / (H * Real.log P) ≤
              20 * (P : ℝ) / (H * Real.log P) := by
            apply (div_le_div_iff_of_pos_right (mul_pos hHpos hlogPpos)).2
            nlinarith
          dsimp only [Sℝ, d, H] at *
          linarith
        · have hopposite :
            (0 < (q.1 : ℝ) * N ∧ (q.2 : ℝ) * N < 0) ∨
              ((q.1 : ℝ) * N < 0 ∧ 0 < (q.2 : ℝ) * N) := by
            rcases lt_or_gt_of_ne hA with hAneg | hApos
            · rcases lt_or_gt_of_ne hB with hBneg | hBpos
              · exact (hsign (Or.inr ⟨hAneg, hBneg⟩)).elim
              · exact Or.inr ⟨hAneg, hBpos⟩
            · rcases lt_or_gt_of_ne hB with hBneg | hBpos
              · exact Or.inl ⟨hApos, hBneg⟩
              · exact (hsign (Or.inl ⟨hApos, hBpos⟩)).elim
          have hsNonneg : 0 ≤ quadraticReciprocalStationaryPoint
              ((q.1 : ℝ) * N) ((q.2 : ℝ) * N) := by
            rcases hopposite with hopposite | hopposite
            · exact (quadraticReciprocalStationaryPoint_pos_of_pos_neg
                hopposite.1 hopposite.2).le
            · exact (quadraticReciprocalStationaryPoint_pos_of_neg_pos
                hopposite.1 hopposite.2).le
          have hq₁ : q.1 ≠ 0 := by
            intro hqzero
            simp [hqzero] at hA
          have hNzero : N ≠ 0 := by
            intro hNzero
            simp [hNzero] at hA
          have hsR :=
            quadraticReciprocalStationaryPoint_same_parameter_le_two_mul
              hq₁ hNzero (le_refl |(q.2 : ℝ)|)
          have hsFar : quadraticReciprocalStationaryPoint
              ((q.1 : ℝ) * N) ((q.2 : ℝ) * N) ≤ (P : ℝ) / 2 := by
            linarith
          have hbound := hstationaryP a b q N N H hPa hab hbP hA hB
            hHfour hsNonneg hsFar hlogLower hhighScale'
            hNupper hMupper
          dsimp only [Sℝ, d, H] at *
          nlinarith

/-- The preceding radius-free estimate applies uniformly throughout the
explicit polylogarithmically growing Fourier box. -/
theorem eventually_specializedFourierMode_Ico_le_highLowMajorant_growing
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (B : ℕ) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      q ∈ fourierFrequencyBox (specializedFourierRadius B P) →
      VinogradovParameterBound ε K P N →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N N 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N N 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S +
          vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S : ℝ)) +
          20 * (P : ℝ) /
            ((Real.log b) ^
                vaughanTypeIILogSavingPhaseExponent ((S : ℝ) + 1) *
              Real.log P) := by
  have hmode :=
    eventually_specializedFourierMode_Ico_le_highLowMajorant_of_phaseBounds
      hPNT hVinogradov (A₀ := 3 * K) (ε := ε / 2)
        (by positivity) (by positivity) (by linarith) S
  have hparams :=
    eventually_vinogradovParameterBounds_of_mem_specializedFourierBox
      B hK hε haexp
  have hradiusScale :=
    eventually_const_mul_log_pow_le_natCast (C := (8 : ℝ)) (by norm_num) B
  have hlogOne : ∀ᶠ P : ℕ in atTop, 1 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hmode, hparams, hradiusScale, hlogOne] with
      P hmodeP hparamsP hradiusScaleP hlogP
  intro a b q N hPa hab hbP hq hN
  have hlogNonneg : 0 ≤ Real.log (P : ℝ) := zero_le_one.trans hlogP
  have hpowOneNat : 1 ≤ (Real.log P) ^ B :=
    one_le_pow₀ hlogP
  have hradius := specializedFourierRadius_lt_log_pow_add_one
    (B := B) (P := P) hlogNonneg
  have hradiusFour : 4 * (specializedFourierRadius B P : ℝ) ≤
      (P : ℝ) := by
    have hfour : 4 * (specializedFourierRadius B P : ℝ) ≤
        8 * (Real.log P) ^ B := by
      linarith
    exact hfour.trans hradiusScaleP
  have hqBounds := mem_fourierFrequencyBox.mp hq
  have hqTwo : |(q.2 : ℝ)| ≤
      (specializedFourierRadius B P : ℝ) := by
    exact_mod_cast hqBounds.2
  have hgeometry : 4 * |(q.2 : ℝ)| ≤ (P : ℝ) :=
    (mul_le_mul_of_nonneg_left hqTwo (by norm_num)).trans hradiusFour
  have hphase := hparamsP q N hq hN
  exact hmodeP a b q N hPa hab hbP hgeometry hphase.1 hphase.2

/-- Arbitrary logarithmic saving, uniform over the growing Fourier box. -/
theorem eventually_specializedFourierMode_Ico_le_logSaving_growing
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (B : ℕ) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      q ∈ fourierFrequencyBox (specializedFourierRadius B P) →
      VinogradovParameterBound ε K P N →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N N 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N N 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S := by
  have hmajor :=
    eventually_specializedFourierMode_Ico_le_highLowMajorant_growing
      hPNT hVinogradov B hK hε haexp (S + 2)
  have hlogLarge : ∀ᶠ P : ℕ in atTop, 60 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 60)
  have hlogSqTop : Tendsto (fun P : ℕ => (Real.log P) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hconstant : ∀ᶠ P : ℕ in atTop,
      3 * vaughanPrimeQuadraticDecayConstant ≤ (Real.log P) ^ 2 :=
    hlogSqTop.eventually
      (eventually_ge_atTop (3 * vaughanPrimeQuadraticDecayConstant))
  filter_upwards [hmajor, hlogLarge, hconstant,
    eventually_ge_atTop (1 : ℕ)] with P hmajorP hlogP hconstantP hP
  intro a b q N hPa hab hbP hq hN
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast hP
  have hPb : P ≤ b := hPa.trans hab.le
  have hlogPpos : 0 < Real.log (P : ℝ) := by linarith
  have hlogPb : Real.log (P : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log hPpos (by exact_mod_cast hPb)
  have hlogbpos : 0 < Real.log (b : ℝ) := hlogPpos.trans_le hlogPb
  let d : ℝ :=
    vaughanTypeIILogSavingPhaseExponent (((S + 2 : ℕ) : ℝ) + 1)
  have hSd : (S : ℝ) ≤ d := by
    dsimp only [d, vaughanTypeIILogSavingPhaseExponent]
    have hScast : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    norm_num
    linarith
  have hpower : (Real.log P) ^ S ≤ (Real.log b) ^ d := by
    calc
      (Real.log P) ^ S ≤ (Real.log b) ^ S :=
        pow_le_pow_left₀ hlogPpos.le hlogPb S
      _ = (Real.log b) ^ (S : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (Real.log b) ^ d :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hSd
  have hsource : 60 * (Real.log P) ^ S ≤
      (Real.log b) ^ d * Real.log P := by
    calc
      60 * (Real.log P) ^ S ≤
          Real.log P * (Real.log P) ^ S :=
        mul_le_mul_of_nonneg_right hlogP (pow_nonneg hlogPpos.le S)
      _ ≤ Real.log P * (Real.log b) ^ d :=
        mul_le_mul_of_nonneg_left hpower hlogPpos.le
      _ = (Real.log b) ^ d * Real.log P := by ring
  have hbound := hmajorP a b q N hPa hab hbP hq hN
  exact hbound.trans (specializedFourierHighLowMajorant_le_logSaving
    vaughanPrimeQuadraticDecayConstant (P : ℝ) (Real.log P)
      ((Real.log b) ^ d) S (Nat.cast_nonneg P) hlogPpos
      (Real.rpow_pos_of_pos hlogbpos d)
      (by nlinarith [sq_nonneg (Real.log P - 60)])
      hconstantP hsource)

/-- Finite Fourier assembly remains uniform for the growing box when the
coefficient family is absolutely summable.  Its retained mass is bounded by
the fixed global `ℓ¹` mass before logarithmic absorption. -/
theorem eventually_specializedFiniteFourierPolynomial_Ico_le_logSaving_growing
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (B : ℕ) (c : ℤ × ℤ → ℂ) (hc : Summable (fun q => ‖c q‖))
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) (Set.Ico (a : ℝ) (b : ℝ))
          (finiteFourierPolynomial
            (fourierFrequencyBox (specializedFourierRadius B P)) c) N N 2 -
        primeEquidistributionIntegral (Set.Ico (a : ℝ) (b : ℝ))
          (finiteFourierPolynomial
            (fourierFrequencyBox (specializedFourierRadius B P)) c) N N 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S := by
  let A : ℝ := ∑' q, ‖c q‖
  have hmode := eventually_specializedFourierMode_Ico_le_logSaving_growing
    hPNT hVinogradov B hK hε haexp (S + 2)
  have hlogSqTop : Tendsto (fun P : ℕ => (Real.log P) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hconstant : ∀ᶠ P : ℕ in atTop, A ≤ (Real.log P) ^ 2 :=
    hlogSqTop.eventually (eventually_ge_atTop A)
  filter_upwards [hmode, hconstant, eventually_ge_atTop (3 : ℕ)] with
      P hmodeP hconstantP hP
  intro a b N hPa hab hbP hN
  have hPtwo : (2 : ℝ) ≤ P := by exact_mod_cast (show 2 ≤ P by omega)
  have hPnonneg : (0 : ℝ) ≤ P := by positivity
  have hlogPpos : 0 < Real.log (P : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hI : Set.Ico (a : ℝ) (b : ℝ) ⊆
      Set.Icc (P : ℝ) (2 * (P : ℝ)) := by
    intro x hx
    constructor
    · have hPaReal : (P : ℝ) ≤ (a : ℝ) := by exact_mod_cast hPa
      exact hPaReal.trans hx.1
    · have hbPReal : (b : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hbP
      exact hx.2.le.trans hbPReal
  have hpoly := norm_finiteFourierPolynomial_discrepancy_le_uniform_of_subset
    hPtwo hI (fourierFrequencyBox (specializedFourierRadius B P)) c N N 2
      (E := (P : ℝ) / (Real.log P) ^ (S + 2))
      (fun q hq => hmodeP a b q N hPa hab hbP hq hN)
  have hmass :
      (∑ q ∈ fourierFrequencyBox (specializedFourierRadius B P), ‖c q‖) ≤ A := by
    dsimp only [A]
    exact Summable.sum_le_tsum _ (fun _ _ => norm_nonneg _) hc
  have hLSpos : 0 < (Real.log P) ^ S := pow_pos hlogPpos S
  have hL2pos : 0 < (Real.log P) ^ 2 := pow_pos hlogPpos 2
  have habsorb : A * ((P : ℝ) / (Real.log P) ^ (S + 2)) ≤
      (P : ℝ) / (Real.log P) ^ S := by
    rw [show (Real.log P) ^ (S + 2) =
      (Real.log P) ^ S * (Real.log P) ^ 2 by rw [pow_add]]
    rw [show A * ((P : ℝ) /
        ((Real.log P) ^ S * (Real.log P) ^ 2)) =
      A * (P : ℝ) / ((Real.log P) ^ S * (Real.log P) ^ 2) by ring]
    apply (div_le_div_iff₀ (mul_pos hLSpos hL2pos) hLSpos).2
    have hmul := mul_le_mul_of_nonneg_right hconstantP
      (mul_nonneg hPnonneg (pow_nonneg hlogPpos.le S))
    convert hmul using 1 <;> ring
  exact hpoly.trans ((mul_le_mul_of_nonneg_right hmass (by positivity)).trans habsorb)

/-- Uniform coefficient-normalized assembly.  Unlike the absorbed form, the
coefficient family is quantified after the eventual scale threshold. -/
theorem eventually_specializedFiniteFourierPolynomial_Ico_le_mass_mul_logSaving_growing
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (B : ℕ) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (c : ℤ × ℤ → ℂ) (a b : ℕ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) (Set.Ico (a : ℝ) (b : ℝ))
          (finiteFourierPolynomial
            (fourierFrequencyBox (specializedFourierRadius B P)) c) N N 2 -
        primeEquidistributionIntegral (Set.Ico (a : ℝ) (b : ℝ))
          (finiteFourierPolynomial
            (fourierFrequencyBox (specializedFourierRadius B P)) c) N N 2‖ ≤
        (∑ q ∈ fourierFrequencyBox (specializedFourierRadius B P), ‖c q‖) *
          ((P : ℝ) / (Real.log P) ^ S) := by
  have hmode := eventually_specializedFourierMode_Ico_le_logSaving_growing
    hPNT hVinogradov B hK hε haexp S
  filter_upwards [hmode, eventually_ge_atTop (2 : ℕ)] with P hmodeP hP
  intro c a b N hPa hab hbP hN
  have hPtwo : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hI : Set.Ico (a : ℝ) (b : ℝ) ⊆
      Set.Icc (P : ℝ) (2 * (P : ℝ)) := by
    intro x hx
    constructor
    · have hPaReal : (P : ℝ) ≤ (a : ℝ) := by exact_mod_cast hPa
      exact hPaReal.trans hx.1
    · have hbPReal : (b : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hbP
      exact hx.2.le.trans hbPReal
  exact norm_finiteFourierPolynomial_discrepancy_le_uniform_of_subset
    hPtwo hI (fourierFrequencyBox (specializedFourierRadius B P)) c N N 2
      (E := (P : ℝ) / (Real.log P) ^ S)
      (fun q hq => hmodeP a b q N hPa hab hbP hq hN)

/-- The growing-box polynomial estimate extends from natural half-open cores
to every measurable order-convex real interval in the dyadic block. -/
theorem eventually_specializedFiniteFourierPolynomial_interval_le_logSaving_growing
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (B : ℕ) (c : ℤ × ℤ → ℂ) (hc : Summable (fun q => ‖c q‖))
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (I : Set ℝ) (N : ℝ),
      MeasurableSet I → OrdConnected I →
      I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial
              (fourierFrequencyBox (specializedFourierRadius B P)) c) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial
              (fourierFrequencyBox (specializedFourierRadius B P)) c) N N 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S := by
  let A : ℝ := ∑' q, ‖c q‖
  have hcore :=
    eventually_specializedFiniteFourierPolynomial_Ico_le_logSaving_growing
      hPNT hVinogradov B c hc hK hε haexp (S + 1)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact tsum_nonneg fun _ => norm_nonneg _
  have habsorb : ∀ᶠ P : ℕ in atTop,
      (4 * A) * (Real.log P) ^ S ≤ P :=
    eventually_const_mul_log_pow_le_natCast (by positivity) S
  have hlogTop : Tendsto (fun P : ℕ => Real.log P) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogTwo : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log P :=
    hlogTop.eventually (eventually_ge_atTop 2)
  filter_upwards [hcore, habsorb, hlogTwo, eventually_ge_atTop (3 : ℕ)] with
      P hcoreP habsorbP hlogPtwo hPthree
  intro I N hImeas hconn hI hN
  let R : ℕ := specializedFourierRadius B P
  have hP : 2 ≤ P := by omega
  have hPnonneg : (0 : ℝ) ≤ P := by positivity
  have hlogP : 0 < Real.log (P : ℝ) := lt_of_lt_of_le (by norm_num) hlogPtwo
  have hlogPow : 0 < (Real.log (P : ℝ)) ^ S := pow_pos hlogP S
  have hmass : (∑ q ∈ fourierFrequencyBox R, ‖c q‖) ≤ A := by
    dsimp only [A]
    exact Summable.sum_le_tsum _ (fun _ _ => norm_nonneg _) hc
  have hcombine :
      (P : ℝ) / (Real.log P) ^ (S + 1) + 2 * A / Real.log P ≤
        (P : ℝ) / (Real.log P) ^ S := by
    apply (le_div_iff₀ hlogPow).2
    have heq :
        ((P : ℝ) / (Real.log P) ^ (S + 1) + 2 * A / Real.log P) *
            (Real.log P) ^ S =
          ((P : ℝ) + 2 * A * (Real.log P) ^ S) / Real.log P := by
      rw [pow_succ]
      field_simp
    rw [heq]
    apply (div_le_iff₀ hlogP).2
    have htwoA : 2 * A * (Real.log P) ^ S ≤ (P : ℝ) := by
      nlinarith [mul_nonneg hA (pow_nonneg hlogP.le S)]
    nlinarith
  by_cases hempty : naturalPointsInDyadicInterval P I = ∅
  · have hemptyBound :=
      norm_specializedFiniteFourierPolynomial_discrepancy_le_of_core_empty
        hP hconn hI hempty R c N
    refine hemptyBound.trans ?_
    calc
      (∑ q ∈ fourierFrequencyBox R, ‖c q‖) / Real.log P ≤
          A / Real.log P := div_le_div_of_nonneg_right hmass hlogP.le
      _ ≤ (P : ℝ) / (Real.log P) ^ (S + 1) + 2 * A / Real.log P := by
        have hsource : 0 ≤ (P : ℝ) / (Real.log P) ^ (S + 1) := by positivity
        calc
          A / Real.log P ≤ 2 * A / Real.log P :=
            (div_le_div_iff_of_pos_right hlogP).2 (by nlinarith)
          _ ≤ (P : ℝ) / (Real.log P) ^ (S + 1) +
              2 * A / Real.log P := le_add_of_nonneg_left hsource
      _ ≤ (P : ℝ) / (Real.log P) ^ S := hcombine
  · have hne : (naturalPointsInDyadicInterval P I).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let a := naturalAnalyticCoreStart P I hne
    let b := naturalAnalyticCoreStop P I hne
    let J : Set ℝ := Set.Ico (a : ℝ) (b : ℝ)
    have hbounds := naturalAnalyticCore_bounds hne
    have hsum := primeEquidistributionSum_eq_analytic_core
      hP hconn hI hne (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2
    change primeEquidistributionSum (P : ℝ) I
        (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 =
      primeEquidistributionSum (P : ℝ) J
        (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 at hsum
    have hendpointRaw :=
      norm_specializedFiniteFourierPolynomial_integral_sub_analyticCore_le
        hP hImeas hconn hI hne R c N
    have hendpoint :
        ‖primeEquidistributionIntegral I
              (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
            primeEquidistributionIntegral J
              (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
          2 * A / Real.log P := by
      refine hendpointRaw.trans ?_
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) hlogP.le
    have hcoreBound :
        ‖primeEquidistributionSum (P : ℝ) J
              (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
            primeEquidistributionIntegral J
              (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
          (P : ℝ) / (Real.log P) ^ (S + 1) := by
      rcases naturalAnalyticCore_start_lt_stop_or_top hne with hab | htop
      · exact hcoreP a b N hbounds.1 hab hbounds.2.2 hN
      · have habEq : a = b := by
          dsimp [a, b]
          omega
        have hJempty : J = ∅ := by simp [J, habEq]
        rw [hJempty]
        simp [primeEquidistributionSum, primesInScaleSet,
          primeEquidistributionIntegral]
        positivity
    calc
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ =
          ‖(primeEquidistributionSum (P : ℝ) J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2) +
            (primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral I
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2)‖ := by
            rw [hsum]
            congr 1
            ring
      _ ≤ ‖primeEquidistributionSum (P : ℝ) J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ +
            ‖primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral I
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ :=
          norm_add_le _ _
      _ ≤ (P : ℝ) / (Real.log P) ^ (S + 1) +
            2 * A / Real.log P :=
          add_le_add hcoreBound (by simpa only [norm_sub_rev] using hendpoint)
      _ ≤ (P : ℝ) / (Real.log P) ^ S := hcombine

/-- Uniform arbitrary-interval assembly with the retained coefficient mass
kept explicit.  The numerical factor three pays for the core and two endpoint
cells, independently of the coefficient family. -/
theorem eventually_specializedFiniteFourierPolynomial_interval_le_three_mass_mul_logSaving_growing
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (B : ℕ) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (c : ℤ × ℤ → ℂ) (I : Set ℝ) (N : ℝ),
      MeasurableSet I → OrdConnected I →
      I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial
              (fourierFrequencyBox (specializedFourierRadius B P)) c) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial
              (fourierFrequencyBox (specializedFourierRadius B P)) c) N N 2‖ ≤
        3 * (∑ q ∈ fourierFrequencyBox
          (specializedFourierRadius B P), ‖c q‖) *
          ((P : ℝ) / (Real.log P) ^ S) := by
  have hcore :=
    eventually_specializedFiniteFourierPolynomial_Ico_le_mass_mul_logSaving_growing
      hPNT hVinogradov B hK hε haexp (S + 1)
  have hscale : ∀ᶠ P : ℕ in atTop, (Real.log P) ^ S ≤ (P : ℝ) :=
    by simpa using
      (eventually_const_mul_log_pow_le_natCast (C := (1 : ℝ)) (by norm_num) S)
  have hlogTwo : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hcore, hscale, hlogTwo, eventually_ge_atTop (3 : ℕ)] with
      P hcoreP hscaleP hlogPtwo hPthree
  intro c I N hImeas hconn hI hN
  let R : ℕ := specializedFourierRadius B P
  let A : ℝ := ∑ q ∈ fourierFrequencyBox R, ‖c q‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hP : 2 ≤ P := by omega
  have hPnonneg : (0 : ℝ) ≤ P := by positivity
  have hlogP : 0 < Real.log (P : ℝ) := lt_of_lt_of_le (by norm_num) hlogPtwo
  have hlogSpos : 0 < (Real.log (P : ℝ)) ^ S := pow_pos hlogP S
  have hlogSuccPos : 0 < (Real.log (P : ℝ)) ^ (S + 1) := pow_pos hlogP _
  have hscalar : (1 : ℝ) / Real.log P ≤
      (P : ℝ) / (Real.log P) ^ (S + 1) := by
    calc
      (1 : ℝ) / Real.log P =
          (Real.log P) ^ S / (Real.log P) ^ (S + 1) := by
        rw [pow_succ]
        field_simp
      _ ≤ (P : ℝ) / (Real.log P) ^ (S + 1) :=
        div_le_div_of_nonneg_right hscaleP hlogSuccPos.le
  have hendpointScale : A / Real.log P ≤
      A * ((P : ℝ) / (Real.log P) ^ (S + 1)) := by
    calc
      A / Real.log P = A * ((1 : ℝ) / Real.log P) := by ring
      _ ≤ A * ((P : ℝ) / (Real.log P) ^ (S + 1)) :=
        mul_le_mul_of_nonneg_left hscalar hA
  have hpowerScale :
      A * ((P : ℝ) / (Real.log P) ^ (S + 1)) ≤
        A * ((P : ℝ) / (Real.log P) ^ S) := by
    have hdenom : (Real.log P) ^ S ≤ (Real.log P) ^ (S + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hlogP.le S)
        (by linarith : 1 ≤ Real.log (P : ℝ))
    have hquot : (P : ℝ) / (Real.log P) ^ (S + 1) ≤
        (P : ℝ) / (Real.log P) ^ S :=
      div_le_div_of_nonneg_left hPnonneg hlogSpos hdenom
    exact mul_le_mul_of_nonneg_left hquot hA
  by_cases hempty : naturalPointsInDyadicInterval P I = ∅
  · have hemptyBound :=
      norm_specializedFiniteFourierPolynomial_discrepancy_le_of_core_empty
        hP hconn hI hempty R c N
    refine hemptyBound.trans ?_
    change A / Real.log P ≤ 3 * A * ((P : ℝ) / (Real.log P) ^ S)
    calc
      A / Real.log P ≤ A * ((P : ℝ) / (Real.log P) ^ (S + 1)) :=
        hendpointScale
      _ ≤ A * ((P : ℝ) / (Real.log P) ^ S) := hpowerScale
      _ ≤ 3 * A * ((P : ℝ) / (Real.log P) ^ S) := by
        have hterm : 0 ≤ A * ((P : ℝ) / (Real.log P) ^ S) := by positivity
        nlinarith
  · have hne : (naturalPointsInDyadicInterval P I).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let a := naturalAnalyticCoreStart P I hne
    let b := naturalAnalyticCoreStop P I hne
    let J : Set ℝ := Set.Ico (a : ℝ) (b : ℝ)
    have hbounds := naturalAnalyticCore_bounds hne
    have hsum := primeEquidistributionSum_eq_analytic_core
      hP hconn hI hne (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2
    change primeEquidistributionSum (P : ℝ) I
        (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 =
      primeEquidistributionSum (P : ℝ) J
        (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 at hsum
    have hendpoint :=
      norm_specializedFiniteFourierPolynomial_integral_sub_analyticCore_le
        hP hImeas hconn hI hne R c N
    change ‖primeEquidistributionIntegral I
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
        primeEquidistributionIntegral J
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
      2 * A / Real.log P at hendpoint
    have hcoreBound :
        ‖primeEquidistributionSum (P : ℝ) J
              (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
            primeEquidistributionIntegral J
              (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
          A * ((P : ℝ) / (Real.log P) ^ (S + 1)) := by
      rcases naturalAnalyticCore_start_lt_stop_or_top hne with hab | htop
      · exact hcoreP c a b N hbounds.1 hab hbounds.2.2 hN
      · have habEq : a = b := by
          dsimp [a, b]
          omega
        have hJempty : J = ∅ := by simp [J, habEq]
        rw [hJempty]
        simp [primeEquidistributionSum, primesInScaleSet,
          primeEquidistributionIntegral]
        positivity
    calc
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ =
          ‖(primeEquidistributionSum (P : ℝ) J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2) +
            (primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral I
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2)‖ := by
            rw [hsum]
            congr 1
            ring
      _ ≤ ‖primeEquidistributionSum (P : ℝ) J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ +
            ‖primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral I
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ :=
          norm_add_le _ _
      _ ≤ A * ((P : ℝ) / (Real.log P) ^ (S + 1)) +
            2 * A / Real.log P := add_le_add hcoreBound
              (by simpa only [norm_sub_rev] using hendpoint)
      _ ≤ 3 * (A * ((P : ℝ) / (Real.log P) ^ (S + 1))) := by
        have htwo : 2 * A / Real.log P ≤
            2 * (A * ((P : ℝ) / (Real.log P) ^ (S + 1))) := by
          calc
            2 * A / Real.log P = 2 * (A / Real.log P) := by ring
            _ ≤ 2 * (A * ((P : ℝ) / (Real.log P) ^ (S + 1))) :=
              mul_le_mul_of_nonneg_left hendpointScale (by norm_num)
        linarith
      _ ≤ 3 * (A * ((P : ℝ) / (Real.log P) ^ S)) := by
        gcongr
      _ = 3 * A * ((P : ℝ) / (Real.log P) ^ S) := by ring

/-- Tao's `C³` norm is nonnegative for the smooth periodic weights under
consideration. -/
theorem taoC3Norm_nonneg_of_smooth
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hper : IsZ2Periodic W) :
    0 ≤ taoC3Norm W := by
  exact (norm_nonneg (W (0, 0))).trans
    (norm_le_taoC3Norm_of_bddAbove W
      (fun i _ => bddAbove_iteratedFDeriv_norm_range W hW hper i) (0, 0))

/-- Every retained coefficient mass is bounded uniformly by the global
cubic radial envelope. -/
theorem sum_norm_taoFourierCoeff_le_taoC3Norm_mul_decayMass
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hper : IsZ2Periodic W) (s : Finset (ℤ × ℤ)) :
    (∑ q ∈ s, ‖taoFourierCoeff W hper hW.continuous q‖) ≤
      27 * taoC3Norm W * (∑' q : ℤ × ℤ, fourierDecayWeight q) := by
  have hC3 : 0 ≤ taoC3Norm W := taoC3Norm_nonneg_of_smooth W hW hper
  have hcoeff :=
    norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_smooth
      W hW hper
  calc
    (∑ q ∈ s, ‖taoFourierCoeff W hper hW.continuous q‖) ≤
        ∑ q ∈ s, 27 * taoC3Norm W * fourierDecayWeight q := by
      exact Finset.sum_le_sum fun q _ => hcoeff q
    _ ≤ ∑' q : ℤ × ℤ, 27 * taoC3Norm W * fourierDecayWeight q := by
      exact Summable.sum_le_tsum _ (fun q _ => mul_nonneg
        (mul_nonneg (by norm_num) hC3) (fourierDecayWeight_nonneg q))
        (summable_fourierDecayWeight.mul_left (27 * taoC3Norm W))
    _ = 27 * taoC3Norm W *
        (∑' q : ℤ × ℤ, fourierDecayWeight q) := by
      rw [tsum_mul_left]

/-- Fully uniform smooth reconstruction at logarithmic radius `2(S+2)`.
All three remaining terms are explicit multiples of `taoC3Norm W`; no
threshold depends on the weight. -/
theorem eventually_specializedSmoothDiscrepancy_le_growingFourierEnvelope
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    let D := ∑' q : ℤ × ℤ, fourierDecayWeight q
    let U := ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q
    ∀ᶠ P : ℕ in atTop,
      ∀ (I : Set ℝ) (W : ℝ × ℝ → ℂ) (N : ℝ),
      MeasurableSet I → OrdConnected I →
      I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) →
      ContDiff ℝ ∞ W → IsZ2Periodic W →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) I W N N 2 -
          primeEquidistributionIntegral I W N N 2‖ ≤
        (2 * (P : ℝ) + 1) *
            (27 * taoC3Norm W * (Real.log P) ^ (-((S + 2 : ℕ) : ℝ)) * U) +
          3 * (27 * taoC3Norm W * D) *
            ((P : ℝ) / (Real.log P) ^ S) +
          ((27 * taoC3Norm W * (Real.log P) ^ (-((S + 2 : ℕ) : ℝ)) * U) /
              Real.log P) * P := by
  dsimp only
  have hpoly :=
    eventually_specializedFiniteFourierPolynomial_interval_le_three_mass_mul_logSaving_growing
      hPNT hVinogradov (2 * (S + 2)) hK hε haexp S
  filter_upwards [hpoly, eventually_ge_atTop (3 : ℕ)] with P hpolyP hP
  intro I W N hImeas hconn hI hW hper hN
  let R : ℕ := specializedFourierRadius (2 * (S + 2)) P
  let c : ℤ × ℤ → ℂ := taoFourierCoeff W hper hW.continuous
  let D : ℝ := ∑' q : ℤ × ℤ, fourierDecayWeight q
  let U : ℝ := ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q
  have hPtwo : 2 ≤ P := by omega
  have hPnonneg : (0 : ℝ) ≤ P := by positivity
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hC3 : 0 ≤ taoC3Norm W := taoC3Norm_nonneg_of_smooth W hW hper
  have hmass := sum_norm_taoFourierCoeff_le_taoC3Norm_mul_decayMass
    W hW hper (fourierFrequencyBox R)
  have hpolyRaw := hpolyP c I N hImeas hconn hI hN
  have hpolyBound :
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
        3 * (27 * taoC3Norm W * D) *
          ((P : ℝ) / (Real.log P) ^ S) := by
    refine hpolyRaw.trans ?_
    dsimp only [R, c, D] at hmass ⊢
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by norm_num)) (by positivity)
  have hraw := norm_specializedSmoothDiscrepancy_le_decayTail
    hPtwo hImeas hI W hW hper R N hpolyBound
  have htail := fourierDecayTail_specializedFourierRadius_le
    (S + 2) hPtwo
  have hDelta :
      27 * taoC3Norm W *
          (∑' q : {q // q ∉ fourierFrequencyBox R}, fourierDecayWeight q) ≤
        27 * taoC3Norm W *
          (Real.log P) ^ (-((S + 2 : ℕ) : ℝ)) * U := by
    dsimp only [R, U] at htail ⊢
    calc
      27 * taoC3Norm W *
          (∑' q : {q // q ∉ fourierFrequencyBox
            (specializedFourierRadius (2 * (S + 2)) P)},
              fourierDecayWeight q) ≤
          27 * taoC3Norm W *
            ((Real.log P) ^ (-((S + 2 : ℕ) : ℝ)) *
              ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q) := by
        gcongr
      _ = 27 * taoC3Norm W * (Real.log P) ^ (-((S + 2 : ℕ) : ℝ)) *
          ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q := by ring
  dsimp only at hraw
  refine hraw.trans ?_
  dsimp only [D, U]
  gcongr

/-- Universal constant left by the growing-box Fourier reconstruction. -/
def specializedFourierReconstructionConstant : ℝ :=
  1 + 81 * (∑' q : ℤ × ℤ, fourierDecayWeight q) +
    108 * (∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q)

theorem specializedFourierReconstructionConstant_pos :
    0 < specializedFourierReconstructionConstant := by
  unfold specializedFourierReconstructionConstant
  have hD : 0 ≤ ∑' q : ℤ × ℤ, fourierDecayWeight q :=
    tsum_nonneg fourierDecayWeight_nonneg
  have hU : 0 ≤ ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q :=
    tsum_nonneg fourierDecayWeightFiveHalves_nonneg
  positivity

/-- Scalar absorption of the three reconstruction terms into one logarithmic
saving with the universal reconstruction constant. -/
theorem growingFourierEnvelope_le_reconstructionConstant
    (S : ℕ) {P L C3 D U : ℝ}
    (hP : 1 ≤ P) (hL : 1 ≤ L) (hC3 : 0 ≤ C3)
    (hU : 0 ≤ U) :
    (2 * P + 1) * (27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) +
        3 * (27 * C3 * D) * (P / L ^ S) +
        ((27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) / L) * P ≤
      (1 + 81 * D + 108 * U) * C3 * P / L ^ S := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hPnonneg : 0 ≤ P := zero_le_one.trans hP
  have hdenom : L ^ S ≤ L ^ (S + 2) := by
    rw [pow_add]
    have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hL
    exact le_mul_of_one_le_right (pow_nonneg hLpos.le S) hLsq
  have hfrac : P / L ^ (S + 2) ≤ P / L ^ S :=
    div_le_div_of_nonneg_left hPnonneg (pow_pos hLpos S) hdenom
  have hdeltaEq : 27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U =
      27 * C3 * U / L ^ (S + 2) := by
    rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
    ring
  have hdeltaNonneg :
      0 ≤ 27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U := by positivity
  have htermOne :
      (2 * P + 1) * (27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) ≤
        81 * U * (C3 * (P / L ^ S)) := by
    calc
      (2 * P + 1) * (27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) ≤
          (3 * P) * (27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) := by
        gcongr
        linarith
      _ = 81 * U * (C3 * (P / L ^ (S + 2))) := by
        rw [hdeltaEq]
        ring
      _ ≤ 81 * U * (C3 * (P / L ^ S)) := by
        gcongr
  have htermThree :
      ((27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) / L) * P ≤
        27 * U * (C3 * (P / L ^ S)) := by
    calc
      ((27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) / L) * P ≤
          (27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) * P := by
        gcongr
        exact div_le_self hdeltaNonneg hL
      _ = 27 * U * (C3 * (P / L ^ (S + 2))) := by
        rw [hdeltaEq]
        ring
      _ ≤ 27 * U * (C3 * (P / L ^ S)) := by
        gcongr
  have hX : 0 ≤ C3 * (P / L ^ S) := by positivity
  have htermTwo : 3 * (27 * C3 * D) * (P / L ^ S) =
      81 * D * (C3 * (P / L ^ S)) := by ring
  calc
    (2 * P + 1) * (27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) +
        3 * (27 * C3 * D) * (P / L ^ S) +
        ((27 * C3 * L ^ (-((S + 2 : ℕ) : ℝ)) * U) / L) * P ≤
      81 * U * (C3 * (P / L ^ S)) +
        81 * D * (C3 * (P / L ^ S)) +
        27 * U * (C3 * (P / L ^ S)) := by
      rw [htermTwo]
      exact add_le_add (add_le_add htermOne le_rfl) htermThree
    _ = (81 * D + 108 * U) * (C3 * (P / L ^ S)) := by ring
    _ ≤ (1 + 81 * D + 108 * U) * (C3 * (P / L ^ S)) := by
      gcongr
      linarith
    _ = (1 + 81 * D + 108 * U) * C3 * P / L ^ S := by ring

/-- Uniform eventual specialized Theorem 2.5 estimate on natural scales,
conditional only on the two analytic prime-sum inputs already isolated by
the development. -/
theorem eventually_specializedSmoothDiscrepancy_le_logSaving_of_analyticInputs
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop,
      ∀ (I : Set ℝ) (W : ℝ × ℝ → ℂ) (N : ℝ),
      MeasurableSet I → OrdConnected I →
      I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) →
      ContDiff ℝ ∞ W → IsZ2Periodic W →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) I W N N 2 -
          primeEquidistributionIntegral I W N N 2‖ ≤
        specializedFourierReconstructionConstant * taoC3Norm W *
          (P : ℝ) / (Real.log P) ^ S := by
  have henvelope :=
    eventually_specializedSmoothDiscrepancy_le_growingFourierEnvelope
      hPNT hVinogradov hK hε haexp S
  have hlogOne : ∀ᶠ P : ℕ in atTop, 1 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [henvelope, hlogOne, eventually_ge_atTop (3 : ℕ)] with
      P henvelopeP hlogP hP
  intro I W N hImeas hconn hI hW hper hN
  have hC3 : 0 ≤ taoC3Norm W := taoC3Norm_nonneg_of_smooth W hW hper
  have hU : 0 ≤ ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q :=
    tsum_nonneg fourierDecayWeightFiveHalves_nonneg
  have hscalar := growingFourierEnvelope_le_reconstructionConstant S
    (P := (P : ℝ)) (L := Real.log P) (C3 := taoC3Norm W)
    (D := ∑' q : ℤ × ℤ, fourierDecayWeight q)
    (U := ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q)
    (by exact_mod_cast (show 1 ≤ P by omega)) hlogP hC3 hU
  exact (henvelopeP I W N hImeas hconn hI hW hper hN).trans
    (by simpa only [specializedFourierReconstructionConstant] using hscalar)

/-- On scales with `log P ≥ 1`, decreasing epsilon only enlarges the
admissible stretched-log parameter range. -/
theorem VinogradovParameterBound.mono_epsilon
    {ε₀ ε K P N : ℝ} (hK : 0 ≤ K) (hlog : 1 ≤ Real.log P)
    (hε : ε₀ ≤ ε) (hN : VinogradovParameterBound ε K P N) :
    VinogradovParameterBound ε₀ K P N := by
  unfold VinogradovParameterBound at hN ⊢
  refine hN.trans ?_
  gcongr

/-- The natural-scale smooth estimate for every positive source epsilon. -/
theorem eventually_specializedSmoothDiscrepancy_le_logSaving_of_analyticInputs'
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop,
      ∀ (I : Set ℝ) (W : ℝ × ℝ → ℂ) (N : ℝ),
      MeasurableSet I → OrdConnected I →
      I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) →
      ContDiff ℝ ∞ W → IsZ2Periodic W →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) I W N N 2 -
          primeEquidistributionIntegral I W N N 2‖ ≤
        specializedFourierReconstructionConstant * taoC3Norm W *
          (P : ℝ) / (Real.log P) ^ S := by
  let ε₀ : ℝ := min ε 1
  have hε₀ : 0 < ε₀ := by
    dsimp only [ε₀]
    exact lt_min hε zero_lt_one
  have hε₀le : ε₀ ≤ ε := by exact min_le_left _ _
  have haexp₀ : 0 ≤ 3 / 2 - ε₀ := by
    have : ε₀ ≤ 1 := min_le_right _ _
    linarith
  have hbase :=
    eventually_specializedSmoothDiscrepancy_le_logSaving_of_analyticInputs
      hPNT hVinogradov hK hε₀ haexp₀ S
  have hlogOne : ∀ᶠ P : ℕ in atTop, 1 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hbase, hlogOne] with P hbaseP hlogP
  intro I W N hImeas hconn hI hW hper hN
  exact hbaseP I W N hImeas hconn hI hW hper
    (VinogradovParameterBound.mono_epsilon hK.le hlogP hε₀le hN)
end

end Tao2026

import Tao2026.LowFrequencyAbsorption
import Tao2026.StationaryFourierSourceBlock
import Tao2026.LinearAxisFourierSourceBlock

/-!
# Specialized finite Fourier-mode partition

This module combines the low-frequency PNT branch with every high-frequency
sign and coordinate-axis chamber for the specialization `M = N`, `j = 2`
used later in Tao's paper.
-/

open Complex Filter Set
open scoped Topology

namespace Tao2026

noncomputable section

/-- Uniform high/low estimate for every mode in one fixed Fourier box, on a
natural half-open dyadic subinterval.  The displayed majorant deliberately
keeps the three eventual absorption terms separate. -/
theorem eventually_specializedFourierMode_Ico_le_highLowMajorant
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (R : ℕ) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      q ∈ fourierFrequencyBox R →
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
  let Sℝ : ℝ := S
  let d : ℝ := vaughanTypeIILogSavingPhaseExponent (Sℝ + 1)
  obtain ⟨D, hsplit⟩ :=
    exists_eventually_reciprocalPhaseScale_low_or_log_rpow_high d
  obtain ⟨C, hC, hlow⟩ :=
    hPNT.eventually_primeFourierMode_sub_integral_Ico_le_logSaving D S
  let A₀ : ℝ := ((R : ℝ) + 1) * K
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; positivity
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
    hzeroQuadratic, hlogTwo, eventually_ge_atTop (4 * R + 2)] with
      P hsplitP hlowP hsameP hstationaryP hzeroLinearP hzeroQuadraticP
      hlogP hPR
  intro a b q N hPa hab hbP hq hN
  have hP2 : 2 ≤ P := by omega
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
  have hparams := vinogradovParameterBounds_of_mem_fourierFrequencyBox
    hN hN hq
  have hNupper : |(q.1 : ℝ) * N| ≤
      A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) := by
    simpa only [A₀, VinogradovParameterBound] using hparams.1
  have hMupper : |(q.2 : ℝ) * N| ≤
      A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) := by
    simpa only [A₀, VinogradovParameterBound] using hparams.2
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
          have hqBounds := mem_fourierFrequencyBox.mp hq
          have hq₂Bound : |(q.2 : ℝ)| ≤ (R : ℝ) := by
            exact_mod_cast hqBounds.2
          have hsR :=
            quadraticReciprocalStationaryPoint_same_parameter_le_two_mul
              hq₁ hNzero hq₂Bound
          have hsFar : quadraticReciprocalStationaryPoint
              ((q.1 : ℝ) * N) ((q.2 : ℝ) * N) ≤ (P : ℝ) / 2 := by
            have hPR' : (4 : ℕ) * R ≤ P := by omega
            have hPRreal : 4 * (R : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPR'
            linarith
          have hbound := hstationaryP a b q N N H hPa hab hbP hA hB
            hHfour hsNonneg hsFar hlogLower hhighScale'
            hNupper hMupper
          dsimp only [Sℝ, d, H] at *
          nlinarith

/-- The three terms in the specialized high/low majorant fit into one target
logarithmic saving once two fixed constants and the source threshold have
been absorbed. -/
theorem specializedFourierHighLowMajorant_le_logSaving
    (C P L Q : ℝ) (S : ℕ)
    (hP : 0 ≤ P) (hL : 0 < L) (hQ : 0 < Q)
    (htail : 3 ≤ L ^ 2) (hconstant : 3 * C ≤ L ^ 2)
    (hsource : 60 * L ^ S ≤ Q * L) :
    P / L ^ (S + 2) + C * P * L ^ (-((S + 2 : ℕ) : ℝ)) +
        20 * P / (Q * L) ≤ P / L ^ S := by
  have hLSpos : 0 < L ^ S := pow_pos hL S
  have hL2pos : 0 < L ^ 2 := pow_pos hL 2
  have hQmulLpos : 0 < Q * L := mul_pos hQ hL
  have hfirst : P / L ^ (S + 2) ≤ P / (3 * L ^ S) := by
    rw [show L ^ (S + 2) = L ^ S * L ^ 2 by rw [pow_add]]
    apply (div_le_div_iff₀ (mul_pos hLSpos hL2pos)
      (mul_pos (by norm_num) hLSpos)).2
    have hmul := mul_le_mul_of_nonneg_left htail
      (mul_nonneg hP (pow_nonneg hL.le S))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hsecondRewrite :
      C * P * L ^ (-((S + 2 : ℕ) : ℝ)) = C * P / L ^ (S + 2) := by
    rw [Real.rpow_neg hL.le, Real.rpow_natCast]
    simp only [div_eq_mul_inv]
  have hsecond : C * P * L ^ (-((S + 2 : ℕ) : ℝ)) ≤
      P / (3 * L ^ S) := by
    rw [hsecondRewrite, show L ^ (S + 2) = L ^ S * L ^ 2 by rw [pow_add]]
    apply (div_le_div_iff₀ (mul_pos hLSpos hL2pos)
      (mul_pos (by norm_num) hLSpos)).2
    have hmul := mul_le_mul_of_nonneg_right hconstant
      (mul_nonneg hP (pow_nonneg hL.le S))
    convert hmul using 1 <;> ring
  have hthird : 20 * P / (Q * L) ≤ P / (3 * L ^ S) := by
    apply (div_le_div_iff₀ hQmulLpos
      (mul_pos (by norm_num) hLSpos)).2
    have hmul := mul_le_mul_of_nonneg_left hsource hP
    convert hmul using 1
    ring
  calc
    _ ≤ P / (3 * L ^ S) + P / (3 * L ^ S) +
        P / (3 * L ^ S) := by gcongr
    _ = P / L ^ S := by ring

/-- Arbitrary logarithmic saving for every Fourier mode in a fixed frequency
box in the specialized `M = N`, `j = 2` phase, uniformly on natural
half-open dyadic subintervals. -/
theorem eventually_specializedFourierMode_Ico_le_logSaving
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (R : ℕ) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      q ∈ fourierFrequencyBox R →
      VinogradovParameterBound ε K P N →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N N 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N N 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S := by
  have hmajor := eventually_specializedFourierMode_Ico_le_highLowMajorant
    hPNT hVinogradov R hK hε haexp (S + 2)
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
      (Real.rpow_pos_of_pos hlogbpos d) (by nlinarith [sq_nonneg (Real.log P - 60)])
      hconstantP hsource)

/-- Finite Fourier-box assembly of the specialized modewise estimate.  The
fixed `ℓ¹` norm of the retained coefficients is absorbed by two additional
logarithmic powers. -/
theorem eventually_specializedFiniteFourierPolynomial_Ico_le_logSaving
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (R : ℕ) (c : ℤ × ℤ → ℂ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) (Set.Ico (a : ℝ) (b : ℝ))
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
        primeEquidistributionIntegral (Set.Ico (a : ℝ) (b : ℝ))
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S := by
  let A : ℝ := ∑ q ∈ fourierFrequencyBox R, ‖c q‖
  have hmode := eventually_specializedFourierMode_Ico_le_logSaving
    hPNT hVinogradov R hK hε haexp (S + 2)
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
    hPtwo hI (fourierFrequencyBox R) c N N 2
      (E := (P : ℝ) / (Real.log P) ^ (S + 2))
      (fun q hq => hmodeP a b q N hPa hab hbP hq hN)
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
  exact hpoly.trans (by simpa only [A] using habsorb)

end

end Tao2026

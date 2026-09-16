import Tao2026.LinearAxisTypeI
import Tao2026.UnequalMangoldtSourceBlock

open ArithmeticFunction Complex Finset Filter Topology
open scoped BigOperators zeta

namespace Tao2026

noncomputable section

/-- Quantitative Mangoldt estimate on the pure-linear coordinate axis.  The
Type I and Type II inputs are the zero-quadratic families, whose Weyl branch
has empty critical set. -/
theorem eventually_norm_mangoldtReciprocalPhaseSum_le_vaughan_logSaving_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {C₀ A₀ ε S : ℝ} (hC₀ : 0 < C₀) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a : ℕ) (N : ℝ),
      0 < P → P ≤ a → a ≤ B → B ≤ 2 * P → N ≠ 0 →
      64 ≤ reciprocalPhaseScale N 0 2 P →
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
        reciprocalPhaseScale N 0 2 P →
      reciprocalPhaseScale N 0 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
        reciprocalPhaseScale N 0 2 (2 * (B : ℝ)) →
      |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖mangoldtReciprocalPhaseSum N 0 2 a B‖ ≤
        vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
  obtain ⟨C₁, hC₁Vin⟩ := hVinogradov
  have hVinogradov' : VinogradovExponentialSumEstimate := ⟨C₁, hC₁Vin⟩
  have hA : (1 / 4 : ℝ) ≤ vaughanTypeIILogSavingVinogradovExponent S := by
    unfold vaughanTypeIILogSavingVinogradovExponent
    linarith
  have hAS : S + 106 ≤
      3 * vaughanTypeIILogSavingVinogradovExponent S := by
    unfold vaughanTypeIILogSavingVinogradovExponent
    linarith
  have hd : 1024 * (S + 105) + 1 ≤
      vaughanTypeIILogSavingPhaseExponent S := by
    unfold vaughanTypeIILogSavingPhaseExponent
    linarith
  have hlogFamily :=
    eventually_norm_weightedConvolutionProductVaughanTypeILogSum_le_logSaving_zero_quadratic
      hA hC₀ hC₁Vin.1 hC₁Vin hε haexp hAS hd
  have hprimeFamily :=
    eventually_norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_logSaving_zero_quadratic
      hA hC₀ hC₁Vin.1 hC₁Vin hε haexp hAS hd
  have hIIFamilyReal :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_explicit_zero_quadratic
      hVinogradov' hA₀ hε haexp hS
  have hIIFamily : ∀ᶠ B : ℕ in atTop,
      ∀ (a : ℕ) (N : ℝ), 0 < B → 2 ≤ Real.log B → N ≠ 0 →
        (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
          reciprocalPhaseScale N 0 2 (2 * (B : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a B) B
            (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff B))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff B))‖ ≤
          vaughanTypeIICanonicalFamilyDecayConstant * (B : ℝ) /
            (Real.log B) ^ S := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hIIFamilyReal]
      with B hB
    intro a N hBpos hlog hN hlower hNupper
    exact hB a B N le_rfl (by
      have hBnonneg : (0 : ℝ) ≤ B := by positivity
      linarith) hBpos hlog hN hlower hNupper
  have hlogLarge : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.log B :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hlogFamily, hprimeFamily, hIIFamily, hlogLarge,
      eventually_ge_atTop (6 : ℕ)] with B hlogB hprimeB hIIB hlogLargeB hB6
  intro P a N hP hPa haB hBP hN h64 hlowerScale hupperScale
    hIILower hNupper
  have hP3 : 3 ≤ P := by omega
  have hcut : vaughanSourceTailCutoff B < a :=
    vaughanSourceTailCutoff_lt_intervalStart hP3 hPa hBP
  have haPos : 0 < a := hP.trans_le hPa
  have hPB : P ≤ B := hPa.trans haB
  have hlogTerm := hlogB P a B N hP hPa haB hBP haPos le_rfl hPB
    hBP hN h64 hlowerScale hupperScale
  have hprimeTerm := hprimeB P a B N hP hPa hBP haPos le_rfl hPB
    hBP hN h64 hlowerScale hupperScale
  have hIITerm := hIIB a N (by omega) hlogLargeB hN hIILower hNupper
  have hassembled := norm_mangoldtReciprocalPhaseSum_le_vaughanComponents_unequal
    N 0 haPos hcut hlogTerm hprimeTerm hIITerm
  have hlogNonneg : 0 ≤ (Real.log B) ^ (-S) :=
    Real.rpow_nonneg (by linarith) _
  calc
    ‖mangoldtReciprocalPhaseSum N 0 2 a B‖ ≤
        typeIQuadraticFamilyDecayConstant * (P : ℝ) *
            (Real.log B) ^ (-S) +
          typeIQuadraticFamilyDecayConstant * (P : ℝ) *
            (Real.log B) ^ (-S) +
          vaughanTypeIICanonicalFamilyDecayConstant * (B : ℝ) /
            (Real.log B) ^ S := hassembled
    _ ≤ vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
      rw [Real.rpow_neg (by linarith : 0 ≤ Real.log B)]
      have hPnonneg : (0 : ℝ) ≤ P := by positivity
      have hBreal : (B : ℝ) ≤ 2 * P := by exact_mod_cast hBP
      have hIIconstant : 0 ≤ vaughanTypeIICanonicalFamilyDecayConstant := by
        unfold vaughanTypeIICanonicalFamilyDecayConstant
        exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      unfold vaughanMangoldtQuadraticDecayConstant
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_right hBreal
        (mul_nonneg hIIconstant
          (inv_nonneg.mpr (Real.rpow_nonneg (by linarith : 0 ≤ Real.log B) S)))]

/-- On the pure-linear axis the reciprocal-phase scale is bounded by the
magnitude of the linear coefficient. -/
theorem reciprocalPhaseScale_zero_quadratic_two_le_abs
    (N : ℝ) {P : ℕ} (hP : 0 < P) :
    reciprocalPhaseScale N 0 2 P ≤ |N| := by
  simpa only [abs_zero, add_zero] using
    (reciprocalPhaseScale_two_le_add_abs N 0 hP)

/-- Source-facing pure-linear Mangoldt estimate with one lower scale condition
at `4P`. -/
theorem eventually_norm_mangoldtReciprocalPhaseSum_le_sourceRange_zero_quadratic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a : ℕ) (N : ℝ),
      0 < P → P ≤ a → a ≤ B → B ≤ 2 * P → N ≠ 0 →
      64 ≤ reciprocalPhaseScale N 0 2 (4 * (P : ℝ)) →
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
        reciprocalPhaseScale N 0 2 (4 * (P : ℝ)) →
      |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖mangoldtReciprocalPhaseSum N 0 2 a B‖ ≤
        vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
  have hbase :=
    eventually_norm_mangoldtReciprocalPhaseSum_le_vaughan_logSaving_zero_quadratic
      hVinogradov (C₀ := A₀) (A₀ := A₀) hA₀ hA₀ hε haexp hS
  filter_upwards [hbase] with B hbaseB
  intro P a N hP hPa haB hBP hN h64 hlower hNupper
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hPfour : (P : ℝ) ≤ 4 * P := by nlinarith
  have hscaleCompareP := reciprocalPhaseScale_anti N 0 2 hPpos hPfour
  have h64P : 64 ≤ reciprocalPhaseScale N 0 2 P := h64.trans hscaleCompareP
  have hlowerP : (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
      reciprocalPhaseScale N 0 2 P := hlower.trans hscaleCompareP
  have hBpos : 0 < B := hP.trans_le (hPa.trans haB)
  have htwoBpos : (0 : ℝ) < 2 * B := by positivity
  have hBPreal : (B : ℝ) ≤ 2 * P := by exact_mod_cast hBP
  have htwoBfourP : (2 : ℝ) * B ≤ 4 * P := by nlinarith
  have hscaleCompareB := reciprocalPhaseScale_anti N 0 2 htwoBpos htwoBfourP
  have hlowerII : (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
      reciprocalPhaseScale N 0 2 (2 * (B : ℝ)) := hlower.trans hscaleCompareB
  have hscaleUpper : reciprocalPhaseScale N 0 2 P ≤
      A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) :=
    (reciprocalPhaseScale_zero_quadratic_two_le_abs N hP).trans hNupper
  exact hbaseB P a N hP hPa haB hBP hN h64P hlowerP hscaleUpper
    hlowerII hNupper

end

end Tao2026

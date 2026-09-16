import Tao2026.UnequalTypeIISourceBlock
import Tao2026.MangoldtSourceBlock

open ArithmeticFunction Complex Finset Filter Topology
open scoped BigOperators zeta

namespace Tao2026

noncomputable section

/-- Exact Vaughan assembly for independent reciprocal-phase coefficients. -/
theorem norm_mangoldtReciprocalPhaseSum_le_vaughanComponents_unequal
    (N M : ℝ) {a b U : ℕ} (ha : 0 < a) (hUa : U < a)
    {Rlog Rprime RII : ℝ}
    (hlog : ‖weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeICoefficient U) log‖ ≤ Rlog)
    (hprime : ‖weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeIPrimeCoefficient U U) (ζ : ArithmeticFunction ℝ)‖ ≤
          Rprime)
    (hII : ‖weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeIIBetaCoefficient U)
        (vaughanTypeIIGammaCoefficient U)‖ ≤ RII) :
    ‖mangoldtReciprocalPhaseSum N M 2 a b‖ ≤ Rlog + Rprime + RII := by
  rw [mangoldtReciprocalPhaseSum_vaughan_source_product_restricted
    N M 2 ha U U]
  rw [weightedRealArithmeticSum_vaughanCutoff_eq_zero_of_lt _ hUa]
  calc
    ‖0 +
        weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeICoefficient U) log -
        weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeIPrimeCoefficient U U) (ζ : ArithmeticFunction ℝ) +
        weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeIIBetaCoefficient U)
          (vaughanTypeIIGammaCoefficient U)‖ ≤
        (‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeICoefficient U) log‖ +
          ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIPrimeCoefficient U U) (ζ : ArithmeticFunction ℝ)‖) +
          ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient U)‖ := by
      simpa only [zero_add] using
        norm_add_le
          (weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeICoefficient U) log -
            weightedConvolutionProductSum (Finset.Ico a b) b
              (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
              (vaughanTypeIPrimeCoefficient U U) (ζ : ArithmeticFunction ℝ))
          (weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient U)) |>.trans
            (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ Rlog + Rprime + RII := add_le_add (add_le_add hlog hprime) hII

/-- Quantitative unequal quadratic Mangoldt estimate obtained by combining the
completed Type I families and the complete unequal Type II family. -/
theorem eventually_norm_mangoldtReciprocalPhaseSum_le_vaughan_logSaving_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {C₀ A₀ ε S : ℝ} (hC₀ : 0 < C₀) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a : ℕ) (N M : ℝ),
      0 < P → P ≤ a → a ≤ B → B ≤ 2 * P → M ≠ 0 →
      64 ≤ reciprocalPhaseScale N M 2 P →
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
        reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale N M 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
        reciprocalPhaseScale N M 2 (2 * (B : ℝ)) →
      |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      |M| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖mangoldtReciprocalPhaseSum N M 2 a B‖ ≤
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
    eventually_norm_weightedConvolutionProductVaughanTypeILogSum_le_logSaving
      hA hC₀ hC₁Vin.1 hC₁Vin hε haexp hAS hd
  have hprimeFamily :=
    eventually_norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_logSaving
      hA hC₀ hC₁Vin.1 hC₁Vin hε haexp hAS hd
  have hIIFamilyReal :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_explicit_unequal
      hVinogradov' hA₀ hε haexp hS
  have hIIFamily : ∀ᶠ B : ℕ in atTop,
      ∀ (a : ℕ) (N M : ℝ), 0 < B → 2 ≤ Real.log B → M ≠ 0 →
        (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
          reciprocalPhaseScale N M 2 (2 * (B : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a B) B
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff B))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff B))‖ ≤
          vaughanTypeIICanonicalFamilyDecayConstant * (B : ℝ) /
            (Real.log B) ^ S := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hIIFamilyReal]
      with B hB
    intro a N M hBpos hlog hM hlower hNupper hMupper
    exact hB a B N M le_rfl (by
      have hBnonneg : (0 : ℝ) ≤ B := by positivity
      linarith) hBpos hlog hM hlower hNupper hMupper
  have hlogLarge : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.log B :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hlogFamily, hprimeFamily, hIIFamily, hlogLarge,
      eventually_ge_atTop (6 : ℕ)] with B hlogB hprimeB hIIB hlogLargeB hB6
  intro P a N M hP hPa haB hBP hM h64 hlowerScale hupperScale
    hIILower hNupper hMupper
  have hP3 : 3 ≤ P := by omega
  have hcut : vaughanSourceTailCutoff B < a :=
    vaughanSourceTailCutoff_lt_intervalStart hP3 hPa hBP
  have haPos : 0 < a := hP.trans_le hPa
  have hPB : P ≤ B := hPa.trans haB
  have hlogTerm := hlogB P a B N M hP hPa haB hBP haPos le_rfl hPB
    hBP hM h64 hlowerScale hupperScale
  have hprimeTerm := hprimeB P a B N M hP hPa hBP haPos le_rfl hPB
    hBP hM h64 hlowerScale hupperScale
  have hIITerm := hIIB a N M (by omega) hlogLargeB hM hIILower
    hNupper hMupper
  have hassembled := norm_mangoldtReciprocalPhaseSum_le_vaughanComponents_unequal
    N M haPos hcut hlogTerm hprimeTerm hIITerm
  have hlogNonneg : 0 ≤ (Real.log B) ^ (-S) :=
    Real.rpow_nonneg (by linarith) _
  calc
    ‖mangoldtReciprocalPhaseSum N M 2 a B‖ ≤
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

/-- At a positive natural scale the unequal quadratic reciprocal-phase scale
is bounded by the sum of the two coefficient magnitudes. -/
theorem reciprocalPhaseScale_two_le_add_abs
    (N M : ℝ) {P : ℕ} (hP : 0 < P) :
    reciprocalPhaseScale N M 2 P ≤ |N| + |M| := by
  have hPone : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hPsqOne : (1 : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith
  have hfirst : |N| / (P : ℝ) ≤ |N| := by
    apply (div_le_iff₀ hPpos).2
    nlinarith [mul_le_mul_of_nonneg_left hPone (abs_nonneg N)]
  have hsecond : |M| / (P : ℝ) ^ 2 ≤ |M| := by
    apply (div_le_iff₀ (sq_pos_of_pos hPpos)).2
    nlinarith [mul_le_mul_of_nonneg_left hPsqOne (abs_nonneg M)]
  unfold reciprocalPhaseScale
  linarith

/-- Source-facing unequal Mangoldt estimate with one lower scale condition at
`4P` and separate coefficient upper bounds. -/
theorem eventually_norm_mangoldtReciprocalPhaseSum_le_sourceRange_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a : ℕ) (N M : ℝ),
      0 < P → P ≤ a → a ≤ B → B ≤ 2 * P → M ≠ 0 →
      64 ≤ reciprocalPhaseScale N M 2 (4 * (P : ℝ)) →
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
        reciprocalPhaseScale N M 2 (4 * (P : ℝ)) →
      |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      |M| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖mangoldtReciprocalPhaseSum N M 2 a B‖ ≤
        vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
  have hbase :=
    eventually_norm_mangoldtReciprocalPhaseSum_le_vaughan_logSaving_unequal
      hVinogradov (C₀ := 2 * A₀) (A₀ := A₀)
      (mul_pos (by norm_num) hA₀) hA₀ hε haexp hS
  filter_upwards [hbase] with B hbaseB
  intro P a N M hP hPa haB hBP hM h64 hlower hNupper hMupper
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hPfour : (P : ℝ) ≤ 4 * P := by nlinarith
  have hscaleCompareP := reciprocalPhaseScale_anti N M 2 hPpos hPfour
  have h64P : 64 ≤ reciprocalPhaseScale N M 2 P := h64.trans hscaleCompareP
  have hlowerP : (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
      reciprocalPhaseScale N M 2 P := hlower.trans hscaleCompareP
  have hBpos : 0 < B := hP.trans_le (hPa.trans haB)
  have htwoBpos : (0 : ℝ) < 2 * B := by positivity
  have hBPreal : (B : ℝ) ≤ 2 * P := by exact_mod_cast hBP
  have htwoBfourP : (2 : ℝ) * B ≤ 4 * P := by nlinarith
  have hscaleCompareB := reciprocalPhaseScale_anti N M 2 htwoBpos htwoBfourP
  have hlowerII : (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
      reciprocalPhaseScale N M 2 (2 * (B : ℝ)) := hlower.trans hscaleCompareB
  have hscaleUpper : reciprocalPhaseScale N M 2 P ≤
      2 * A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) := by
    calc
      reciprocalPhaseScale N M 2 P ≤ |N| + |M| :=
        reciprocalPhaseScale_two_le_add_abs N M hP
      _ ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) +
          A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) :=
        add_le_add hNupper hMupper
      _ = 2 * A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) := by ring
  exact hbaseB P a N M hP hPa haB hBP hM h64P hlowerP hscaleUpper
    hlowerII hNupper hMupper

end

end Tao2026

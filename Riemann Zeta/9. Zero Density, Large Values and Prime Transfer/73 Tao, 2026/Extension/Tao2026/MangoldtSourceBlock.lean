import Tao2026.TypeISourceBlock

/-!
# Canonical Mangoldt source-block assembly

This module combines the completed Type I and Type II Vaughan estimates at
the canonical cube-root cutoff.  The first theorem is the exact finite
triangle-inequality interface; the final theorem inserts the quantitative
quadratic estimates with one shared logarithmic exponent.
-/

open ArithmeticFunction Complex Finset Filter Topology
open scoped BigOperators zeta

namespace Tao2026

noncomputable section

/-- The initial cutoff term in Vaughan's identity vanishes once the interval
starts strictly above the cutoff. -/
theorem weightedRealArithmeticSum_vaughanCutoff_eq_zero_of_lt
    {a b V : ℕ} (w : ℕ → ℂ) (hVa : V < a) :
    weightedRealArithmeticSum (Finset.Ico a b) w
      (arithmeticFunctionCutoff Λ V) = 0 := by
  unfold weightedRealArithmeticSum
  apply Finset.sum_eq_zero
  intro n hn
  have han : a ≤ n := (Finset.mem_Ico.mp hn).1
  have hVn : ¬n ≤ V := Nat.not_le_of_lt (hVa.trans_le han)
  simp [arithmeticFunctionCutoff_apply, hVn]

/-- Exact assembly of the three nonzero source-oriented Vaughan components.
The subtraction in the second Type I term costs only its norm. -/
theorem norm_mangoldtReciprocalPhaseSum_le_vaughanComponents
    (N : ℝ) {a b U : ℕ} (ha : 0 < a) (hUa : U < a)
    {Rlog Rprime RII : ℝ}
    (hlog : ‖weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
        (vaughanTypeICoefficient U) log‖ ≤ Rlog)
    (hprime : ‖weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
        (vaughanTypeIPrimeCoefficient U U) (ζ : ArithmeticFunction ℝ)‖ ≤
          Rprime)
    (hII : ‖weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
        (vaughanTypeIIBetaCoefficient U)
        (vaughanTypeIIGammaCoefficient U)‖ ≤ RII) :
    ‖mangoldtReciprocalPhaseSum N N 2 a b‖ ≤ Rlog + Rprime + RII := by
  rw [mangoldtReciprocalPhaseSum_vaughan_source_product_restricted
    N N 2 ha U U]
  rw [weightedRealArithmeticSum_vaughanCutoff_eq_zero_of_lt _ hUa]
  calc
    ‖0 +
        weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeICoefficient U) log -
        weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIPrimeCoefficient U U) (ζ : ArithmeticFunction ℝ) +
        weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIIBetaCoefficient U)
          (vaughanTypeIIGammaCoefficient U)‖ ≤
        (‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeICoefficient U) log‖ +
          ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIPrimeCoefficient U U) (ζ : ArithmeticFunction ℝ)‖) +
          ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient U)‖ := by
      simpa only [zero_add] using
        norm_add_le
          (weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeICoefficient U) log -
            weightedConvolutionProductSum (Finset.Ico a b) b
              (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
              (vaughanTypeIPrimeCoefficient U U) (ζ : ArithmeticFunction ℝ))
          (weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient U)) |>.trans
            (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ Rlog + Rprime + RII := add_le_add (add_le_add hlog hprime) hII

/-- Combined decay constant for the two Type I components and the Type II
component after replacing the upper endpoint by at most twice the dyadic
scale. -/
noncomputable def vaughanMangoldtQuadraticDecayConstant : ℝ :=
  2 * (typeIQuadraticFamilyDecayConstant +
    vaughanTypeIICanonicalFamilyDecayConstant)

theorem vaughanMangoldtQuadraticDecayConstant_pos :
    0 < vaughanMangoldtQuadraticDecayConstant := by
  have hII : 0 ≤ vaughanTypeIICanonicalFamilyDecayConstant := by
    unfold vaughanTypeIICanonicalFamilyDecayConstant
    exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  unfold vaughanMangoldtQuadraticDecayConstant
  nlinarith [typeIQuadraticFamilyDecayConstant_pos]

/-- The canonical cutoff lies below the interval start on every sufficiently
large dyadic source block. -/
theorem vaughanSourceTailCutoff_lt_intervalStart
    {P a B : ℕ} (hP : 3 ≤ P) (hPa : P ≤ a) (hBP : B ≤ 2 * P) :
    vaughanSourceTailCutoff B < a := by
  have hsq := vaughanSourceTailCutoff_sq_le B
  have hcutP : vaughanSourceTailCutoff B < P := by
    by_contra h
    have hPcut : P ≤ vaughanSourceTailCutoff B := Nat.le_of_not_gt h
    have hPtwo : P ^ 2 ≤ B :=
      (Nat.pow_le_pow_left hPcut 2).trans hsq
    have : P ^ 2 ≤ 2 * P := hPtwo.trans hBP
    nlinarith
  exact hcutP.trans_le hPa

/-- Quantitative quadratic Mangoldt sum obtained by inserting the completed
Type I and Type II estimates into Vaughan's identity.  The hypotheses expose
the two equivalent source-scale lower/upper descriptions currently used by
the two analytic branches; eliminating that duplication is a later interface
simplification, not an analytic gap. -/
theorem eventually_norm_mangoldtReciprocalPhaseSum_le_vaughan_logSaving
    (hVinogradov : VinogradovExponentialSumEstimate)
    {C₀ A₀ ε S : ℝ} (hC₀ : 0 < C₀) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a : ℕ) (N : ℝ),
      0 < P → P ≤ a → a ≤ B → B ≤ 2 * P → N ≠ 0 →
      64 ≤ reciprocalPhaseScale N N 2 P →
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤
        reciprocalPhaseScale N N 2 P →
      reciprocalPhaseScale N N 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      2 * (B : ℝ) *
          (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤ |N| →
      |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖mangoldtReciprocalPhaseSum N N 2 a B‖ ≤
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
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_explicit
      hVinogradov' hA₀ hε haexp hS
  have hIIFamily : ∀ᶠ B : ℕ in atTop,
      ∀ (a : ℕ) (N : ℝ), 0 < B → 2 ≤ Real.log B → N ≠ 0 →
        2 * (B : ℝ) *
            (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a B) B
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff B))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff B))‖ ≤
          vaughanTypeIICanonicalFamilyDecayConstant * (B : ℝ) /
            (Real.log B) ^ S := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hIIFamilyReal]
      with B hB
    intro a N hBpos hlog hN hlower hupper
    exact hB a B N le_rfl (by
      have hBnonneg : (0 : ℝ) ≤ B := by positivity
      linarith) hBpos hlog hN hlower hupper
  have hlogLarge : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.log B :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hlogFamily, hprimeFamily, hIIFamily, hlogLarge,
      eventually_ge_atTop (6 : ℕ)] with B hlogB hprimeB hIIB hlogLargeB hB6
  intro P a N hP hPa haB hBP hN h64 hlowerScale hupperScale
    hlowerN hupperN
  have hP3 : 3 ≤ P := by omega
  have hcut : vaughanSourceTailCutoff B < a :=
    vaughanSourceTailCutoff_lt_intervalStart hP3 hPa hBP
  have haPos : 0 < a := hP.trans_le hPa
  have hPB : P ≤ B := hPa.trans haB
  have hlogTerm := hlogB P a B N N hP hPa haB hBP haPos le_rfl hPB
    hBP hN h64 hlowerScale hupperScale
  have hprimeTerm := hprimeB P a B N N hP hPa hBP haPos le_rfl hPB
    hBP hN h64 hlowerScale hupperScale
  have hIITerm := hIIB a N (by omega) hlogLargeB hN hlowerN hupperN
  have hassembled := norm_mangoldtReciprocalPhaseSum_le_vaughanComponents
    N haPos hcut hlogTerm hprimeTerm hIITerm
  have hlogNonneg : 0 ≤ (Real.log B) ^ (-S) := Real.rpow_nonneg (by linarith) _
  calc
    ‖mangoldtReciprocalPhaseSum N N 2 a B‖ ≤
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

/-- For a positive natural scale, the self-quadratic reciprocal phase scale
is at most twice the absolute frequency. -/
theorem reciprocalPhaseScale_self_two_le_two_abs
    (N : ℝ) {P : ℕ} (hP : 0 < P) :
    reciprocalPhaseScale N N 2 P ≤ 2 * |N| := by
  have hPone : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hPsqOne : (1 : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith
  have hfirst : |N| / (P : ℝ) ≤ |N| := by
    apply (div_le_iff₀ hPpos).2
    nlinarith [mul_le_mul_of_nonneg_left hPone (abs_nonneg N)]
  have hsecond : |N| / (P : ℝ) ^ 2 ≤ |N| := by
    apply (div_le_iff₀ (sq_pos_of_pos hPpos)).2
    nlinarith [mul_le_mul_of_nonneg_left hPsqOne (abs_nonneg N)]
  unfold reciprocalPhaseScale
  linarith

/-- A source lower bound on the absolute quadratic frequency supplies the
logarithmic lower bound for the reciprocal phase scale. -/
theorem logPower_le_reciprocalPhaseScale_self_two_of_abs_lower
    {N d : ℝ} {P B : ℕ} (hP : 0 < P) (hPB : P ≤ B)
    (hlogPower : 0 ≤ (Real.log B) ^ d)
    (hN : 2 * (B : ℝ) * (Real.log B) ^ d ≤ |N|) :
    (Real.log B) ^ d ≤ reciprocalPhaseScale N N 2 P := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hPBreal : (P : ℝ) ≤ B := by exact_mod_cast hPB
  have hmul : (P : ℝ) * (Real.log B) ^ d ≤ |N| := by
    calc
      (P : ℝ) * (Real.log B) ^ d ≤
          2 * (B : ℝ) * (Real.log B) ^ d := by
        exact mul_le_mul_of_nonneg_right (by linarith) hlogPower
      _ ≤ |N| := hN
  have hdiv : (Real.log B) ^ d ≤ |N| / (P : ℝ) :=
    (le_div_iff₀ hPpos).2 (by simpa [mul_comm] using hmul)
  exact hdiv.trans (le_add_of_nonneg_right
    (div_nonneg (abs_nonneg N) (sq_nonneg (P : ℝ))))

/-- The explicit common phase exponent is already large enough that
`log(B)^d` exceeds 32 as soon as `log B ≥ 2`. -/
theorem thirtyTwo_le_log_rpow_vaughanTypeIILogSavingPhaseExponent
    {B : ℕ} {S : ℝ} (hS : 0 ≤ S) (hlog : 2 ≤ Real.log B) :
    (32 : ℝ) ≤
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S := by
  have hd : (5 : ℝ) ≤ vaughanTypeIILogSavingPhaseExponent S := by
    unfold vaughanTypeIILogSavingPhaseExponent
    linarith
  calc
    (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by norm_num
    _ ≤ (Real.log B) ^ (5 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hlog (by norm_num)
    _ ≤ (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hd

/-- The single source lower frequency bound also gives the absolute Type I
threshold `64 ≤ F`. -/
theorem sixtyFour_le_reciprocalPhaseScale_self_two_of_abs_lower
    {N : ℝ} {P B : ℕ} {S : ℝ} (hP : 0 < P) (hPB : P ≤ B)
    (hS : 0 ≤ S) (hlog : 2 ≤ Real.log B)
    (hN : 2 * (B : ℝ) *
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤ |N|) :
    64 ≤ reciprocalPhaseScale N N 2 P := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hPBreal : (P : ℝ) ≤ B := by exact_mod_cast hPB
  have hpow :=
    thirtyTwo_le_log_rpow_vaughanTypeIILogSavingPhaseExponent hS hlog
  have hmul : (64 : ℝ) * P ≤ |N| := by
    calc
      (64 : ℝ) * P ≤ 2 * (B : ℝ) * 32 := by nlinarith
      _ ≤ 2 * (B : ℝ) *
          (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S := by
        gcongr
      _ ≤ |N| := hN
  have hdiv : (64 : ℝ) ≤ |N| / (P : ℝ) :=
    (le_div_iff₀ hPpos).2 (by simpa [mul_comm] using hmul)
  exact hdiv.trans (le_add_of_nonneg_right
    (div_nonneg (abs_nonneg N) (sq_nonneg (P : ℝ))))

/-- Source-facing quadratic Mangoldt estimate with one lower and one upper
frequency bound.  All reciprocal-phase-scale hypotheses in the preceding
assembly theorem are derived internally. -/
theorem eventually_norm_mangoldtReciprocalPhaseSum_le_sourceRange
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a : ℕ) (N : ℝ),
      0 < P → P ≤ a → a ≤ B → B ≤ 2 * P → N ≠ 0 →
      2 * (B : ℝ) *
          (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S ≤ |N| →
      |N| ≤ A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖mangoldtReciprocalPhaseSum N N 2 a B‖ ≤
        vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
  have hbase :=
    eventually_norm_mangoldtReciprocalPhaseSum_le_vaughan_logSaving
      hVinogradov (C₀ := 2 * A₀) (A₀ := A₀)
      (mul_pos (by norm_num) hA₀) hA₀ hε haexp hS
  have hlogLarge : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.log B :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hbase, hlogLarge] with B hbaseB hlogB
  intro P a N hP hPa haB hBP hN hlower hupper
  have hPB : P ≤ B := hPa.trans haB
  have hphaseNonneg : 0 ≤
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S :=
    Real.rpow_nonneg (by linarith) _
  have h64 := sixtyFour_le_reciprocalPhaseScale_self_two_of_abs_lower
    hP hPB hS hlogB hlower
  have hscaleLower :=
    logPower_le_reciprocalPhaseScale_self_two_of_abs_lower
      hP hPB hphaseNonneg hlower
  have hscaleUpper : reciprocalPhaseScale N N 2 P ≤
      2 * A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) := by
    calc
      reciprocalPhaseScale N N 2 P ≤ 2 * |N| :=
        reciprocalPhaseScale_self_two_le_two_abs N hP
      _ ≤ 2 * (A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε))) := by
        gcongr
      _ = 2 * A₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) := by ring
  exact hbaseB P a N hP hPa haB hBP hN h64 hscaleLower hscaleUpper
    hlower hupper

end

end Tao2026

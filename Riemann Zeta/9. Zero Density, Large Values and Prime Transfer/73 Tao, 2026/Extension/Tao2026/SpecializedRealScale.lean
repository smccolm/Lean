import Tao2026.SpecializedGrowingFourier

/-!
# Real-scale closure of the specialized prime equidistribution estimate

This module bridges the natural dyadic scale used by the Fourier argument to
the literal real scale in `TaoTheorem25SpecializedConclusion`.  The bridge uses
the natural ceiling of the real scale.  Its lower endpoint changes by less
than one, so the sampled prime sum is unchanged and the logarithmic integral
incurs only a unit-cell error.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace Tao2026

noncomputable section

/-- The natural dyadic scale immediately above a real source scale. -/
def specializedRealScaleCeil (P : ℝ) : ℕ := ⌈P⌉₊

/-- The part of a real source interval lying above its natural ceiling. -/
def specializedRealScaleCore (P : ℝ) (I : Set ℝ) : Set ℝ :=
  I ∩ Set.Ici (specializedRealScaleCeil P : ℝ)

theorem specializedRealScaleCeil_bounds {P : ℝ} (hP : 0 ≤ P) :
    P ≤ (specializedRealScaleCeil P : ℝ) ∧
      (specializedRealScaleCeil P : ℝ) < P + 1 := by
  exact ⟨Nat.le_ceil P, Nat.ceil_lt_add_one hP⟩

theorem two_le_specializedRealScaleCeil {P : ℝ} (hP : 2 ≤ P) :
    2 ≤ specializedRealScaleCeil P := by
  have hcast : (2 : ℝ) ≤ (specializedRealScaleCeil P : ℝ) :=
    hP.trans (Nat.le_ceil P)
  exact_mod_cast hcast

theorem specializedRealScaleCore_measurable {P : ℝ} {I : Set ℝ}
    (hI : MeasurableSet I) : MeasurableSet (specializedRealScaleCore P I) := by
  exact hI.inter measurableSet_Ici

theorem specializedRealScaleCore_ordConnected {P : ℝ} {I : Set ℝ}
    (hI : OrdConnected I) : OrdConnected (specializedRealScaleCore P I) := by
  exact hI.inter ordConnected_Ici

theorem specializedRealScaleCore_subset_dyadic
    {P : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Icc P (2 * P)) :
    specializedRealScaleCore P I ⊆
      Set.Icc (specializedRealScaleCeil P : ℝ)
        (2 * (specializedRealScaleCeil P : ℝ)) := by
  intro x hx
  refine ⟨hx.2, ?_⟩
  exact (hI hx.1).2.trans
    (mul_le_mul_of_nonneg_left (Nat.le_ceil P) (by norm_num))

/-- Moving a real dyadic scale to its natural ceiling preserves its sampled
prime set exactly. -/
theorem primesInScaleSet_eq_realScaleCore
    {P : ℝ} {I : Set ℝ} (hP : 2 ≤ P)
    (hI : I ⊆ Set.Icc P (2 * P)) :
    primesInScaleSet P I =
      primesInScaleSet (specializedRealScaleCeil P : ℝ)
        (specializedRealScaleCore P I) := by
  classical
  have hQ : (2 : ℝ) ≤ specializedRealScaleCeil P := by
    exact_mod_cast two_le_specializedRealScaleCeil hP
  have hcore := specializedRealScaleCore_subset_dyadic hI
  ext p
  rw [mem_primesInScaleSet hP hI, mem_primesInScaleSet hQ hcore]
  constructor
  · rintro ⟨hp, hpI⟩
    refine ⟨hp, hpI, ?_⟩
    have hpLower : P ≤ (p : ℝ) := (hI hpI).1
    show (specializedRealScaleCeil P : ℝ) ≤ (p : ℝ)
    exact_mod_cast (Nat.ceil_le.mpr hpLower)
  · rintro ⟨hp, hpI, _hpLower⟩
    exact ⟨hp, hpI⟩

theorem primeEquidistributionSum_eq_realScaleCore
    {P : ℝ} {I : Set ℝ} (hP : 2 ≤ P)
    (hI : I ⊆ Set.Icc P (2 * P))
    (W : ℝ × ℝ → ℂ) (N M : ℝ) (j : ℕ) :
    primeEquidistributionSum P I W N M j =
      primeEquidistributionSum (specializedRealScaleCeil P : ℝ)
        (specializedRealScaleCore P I) W N M j := by
  unfold primeEquidistributionSum
  rw [primesInScaleSet_eq_realScaleCore hP hI]

theorem symmDiff_specializedRealScaleCore_subset
    {P : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Icc P (2 * P)) :
    symmDiff I (specializedRealScaleCore P I) ⊆
      Set.Icc P (specializedRealScaleCeil P : ℝ) := by
  intro x hx
  rcases Set.mem_symmDiff.mp hx with hx | hx
  · refine ⟨(hI hx.1).1, ?_⟩
    by_contra hnot
    have hxLower : (specializedRealScaleCeil P : ℝ) ≤ x :=
      le_of_not_ge hnot
    exact hx.2 ⟨hx.1, hxLower⟩
  · exact False.elim (hx.2 hx.1.1)

/-- The endpoint strip discarded by the real-to-natural scale bridge has
Lebesgue measure at most one. -/
theorem volumeReal_symmDiff_specializedRealScaleCore_le_one
    {P : ℝ} {I : Set ℝ} (hP : 0 ≤ P)
    (hI : I ⊆ Set.Icc P (2 * P)) :
    volume.real (symmDiff I (specializedRealScaleCore P I)) ≤ 1 := by
  have hsubset := symmDiff_specializedRealScaleCore_subset hI
  have hmeasure :
      volume.real (symmDiff I (specializedRealScaleCore P I)) ≤
        volume.real (Set.Icc P (specializedRealScaleCeil P : ℝ)) :=
    measureReal_mono hsubset (by simp [Real.volume_Icc])
  have hnonneg : 0 ≤ (specializedRealScaleCeil P : ℝ) - P :=
    sub_nonneg.mpr (Nat.le_ceil P)
  have hvolume :
      volume.real (Set.Icc P (specializedRealScaleCeil P : ℝ)) =
        (specializedRealScaleCeil P : ℝ) - P := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hnonneg]
  rw [hvolume] at hmeasure
  exact hmeasure.trans (le_of_lt (sub_lt_iff_lt_add.mpr
    (by simpa [specializedRealScaleCeil, add_comm] using
      (Nat.ceil_lt_add_one hP))))

/-- The real-to-natural endpoint bridge costs at most one logarithmically
weighted unit cell, uniformly in the frequency parameter. -/
theorem norm_primeEquidistributionIntegral_sub_realScaleCore_le
    {P : ℝ} {I : Set ℝ} (hP : 2 ≤ P) (hImeas : MeasurableSet I)
    (hI : I ⊆ Set.Icc P (2 * P))
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hper : IsZ2Periodic W)
    (N M : ℝ) (j : ℕ) :
    ‖primeEquidistributionIntegral I W N M j -
        primeEquidistributionIntegral (specializedRealScaleCore P I)
          W N M j‖ ≤
      taoC3Norm W / Real.log P := by
  have hPnonneg : 0 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hC3 : 0 ≤ taoC3Norm W := taoC3Norm_nonneg_of_smooth W hW hper
  have hbdd : ∀ x : ℝ × ℝ, ‖W x‖ ≤ taoC3Norm W := fun x =>
    norm_le_taoC3Norm_of_bddAbove W
      (fun i _ => bddAbove_iteratedFDeriv_norm_range W hW hper i) x
  have hfI := integrableOn_primeEquidistributionIntegrand
    hP hI hW.continuous N M j
  have hfCore : IntegrableOn
      (fun t => W (N / t, M / t ^ j) / Real.log t)
      (specializedRealScaleCore P I) :=
    hfI.mono_set inter_subset_left
  have hIfinite : volume I ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono hI)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hCorefinite : volume (specializedRealScaleCore P I) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_left hIfinite
  have hpoint : ∀ t ∈ symmDiff I (specializedRealScaleCore P I),
      ‖W (N / t, M / t ^ j) / Real.log t‖ ≤
        taoC3Norm W / Real.log P := by
    intro t ht
    have htBounds := symmDiff_specializedRealScaleCore_subset hI ht
    have htpos : 0 < t := hPpos.trans_le htBounds.1
    have htone : 1 < t := lt_of_lt_of_le (by norm_num) (hP.trans htBounds.1)
    have hlogt : 0 < Real.log t := Real.log_pos htone
    have hlogmono : Real.log P ≤ Real.log t :=
      Real.strictMonoOn_log.monotoneOn hPpos htpos htBounds.1
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hlogt]
    calc
      ‖W (N / t, M / t ^ j)‖ / Real.log t ≤
          taoC3Norm W / Real.log t :=
        (div_le_div_iff_of_pos_right hlogt).2 (hbdd _)
      _ ≤ taoC3Norm W / Real.log P :=
        div_le_div_of_nonneg_left hC3 hlogP hlogmono
  unfold primeEquidistributionIntegral
  have hraw := norm_setIntegral_sub_setIntegral_le_symmDiff
    hImeas (specializedRealScaleCore_measurable hImeas)
    hfI hfCore hIfinite hCorefinite hpoint
  exact hraw.trans (mul_le_of_le_one_right (div_nonneg hC3 hlogP.le)
    (volumeReal_symmDiff_specializedRealScaleCore_le_one hPnonneg hI))

/-- Increasing the dyadic scale preserves an admissible Vinogradov parameter
when the stretched-log exponent is nonnegative. -/
theorem VinogradovParameterBound.mono_scale
    {ε K P Q N : ℝ} (hK : 0 ≤ K) (hexp : 0 ≤ 3 / 2 - ε)
    (hP : 1 ≤ P) (hPQ : P ≤ Q)
    (hN : VinogradovParameterBound ε K P N) :
    VinogradovParameterBound ε K Q N := by
  unfold VinogradovParameterBound at hN ⊢
  refine hN.trans ?_
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQpos : 0 < Q := hPpos.trans_le hPQ
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hlogmono : Real.log P ≤ Real.log Q := Real.log_le_log hPpos hPQ
  have hpow : (Real.log P) ^ (3 / 2 - ε) ≤
      (Real.log Q) ^ (3 / 2 - ε) :=
    Real.rpow_le_rpow hlogP hlogmono hexp
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) hK

/-- Every fixed real logarithmic power is eventually at most the identity. -/
theorem eventually_log_rpow_le_self (A : ℝ) :
    ∀ᶠ P : ℝ in atTop, (Real.log P) ^ A ≤ P := by
  have hsmall := isLittleO_log_rpow_rpow_atTop A
    (s := (1 : ℝ)) zero_lt_one
  have hdenPositive : ∀ᶠ P : ℝ in atTop, 0 < ‖P ^ (1 : ℝ)‖ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hP)]
    exact zero_lt_one.trans hP
  filter_upwards
      [hsmall.eventuallyLT_norm_of_eventually_pos hdenPositive,
        eventually_ge_atTop (1 : ℝ)] with P hsmallP hP
  have hlog : 0 ≤ Real.log P := Real.log_nonneg hP
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog A), Real.rpow_one,
    Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hP)] at hsmallP
  exact hsmallP.le

/-- Universal constant after transferring the growing Fourier estimate from
the natural ceiling back to a real source scale. -/
def specializedRealScaleReconstructionConstant : ℝ :=
  2 * specializedFourierReconstructionConstant + 1

theorem specializedRealScaleReconstructionConstant_pos :
    0 < specializedRealScaleReconstructionConstant := by
  unfold specializedRealScaleReconstructionConstant
  linarith [specializedFourierReconstructionConstant_pos]

/-- The natural-ceiling main term is controlled by the requested real
logarithmic exponent. -/
theorem naturalCeil_logSaving_le_real_logSaving
    {P A : ℝ} {S : ℕ} (hP : 1 ≤ P) (hlogPone : 1 ≤ Real.log P)
    (hA : A ≤ S) :
    (specializedRealScaleCeil P : ℝ) /
        (Real.log (specializedRealScaleCeil P : ℝ)) ^ S ≤
      2 * P / (Real.log P) ^ A := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQpos : (0 : ℝ) < specializedRealScaleCeil P :=
    hPpos.trans_le (Nat.le_ceil P)
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hPgtOne : 1 < P :=
    (Real.log_pos_iff hPpos.le).mp (zero_lt_one.trans_le hlogPone)
  have hlogmono : Real.log P ≤
      Real.log (specializedRealScaleCeil P : ℝ) :=
    Real.log_le_log hPpos (Nat.le_ceil P)
  have hrealToNat : (Real.log P) ^ A ≤ (Real.log P) ^ S := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlogPone hA
  have hdenom : (Real.log P) ^ A ≤
      (Real.log (specializedRealScaleCeil P : ℝ)) ^ S := by
    exact hrealToNat.trans (pow_le_pow_left₀ hlogP hlogmono S)
  have hdenomPos : 0 <
      (Real.log (specializedRealScaleCeil P : ℝ)) ^ S := by
    have : 0 < Real.log (specializedRealScaleCeil P : ℝ) :=
      Real.log_pos (hPgtOne.trans_le (Nat.le_ceil P))
    positivity
  have hrealDenomPos : 0 < (Real.log P) ^ A :=
    Real.rpow_pos_of_pos (Real.log_pos hPgtOne) A
  have hQle : (specializedRealScaleCeil P : ℝ) ≤ 2 * P := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ P by positivity)
    change (specializedRealScaleCeil P : ℝ) < P + 1 at hceil
    linarith
  calc
    (specializedRealScaleCeil P : ℝ) /
        (Real.log (specializedRealScaleCeil P : ℝ)) ^ S ≤
      (specializedRealScaleCeil P : ℝ) / (Real.log P) ^ A :=
        div_le_div_of_nonneg_left hQpos.le hrealDenomPos hdenom
    _ ≤ 2 * P / (Real.log P) ^ A :=
      div_le_div_of_nonneg_right hQle hrealDenomPos.le

/-- Eventual specialized Theorem 2.5 estimate on literal real scales and for
an arbitrary positive real logarithmic saving exponent. -/
theorem eventually_specializedSmoothDiscrepancy_le_real_logSaving_of_analyticInputs
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    {K ε A : ℝ} (hK : 0 < K) (hε : 0 < ε) (_hA : 0 < A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (I : Set ℝ) (W : ℝ × ℝ → ℂ) (N : ℝ),
      MeasurableSet I → OrdConnected I → I ⊆ Set.Icc P (2 * P) →
      ContDiff ℝ ∞ W → IsZ2Periodic W →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum P I W N N 2 -
          primeEquidistributionIntegral I W N N 2‖ ≤
        specializedRealScaleReconstructionConstant * taoC3Norm W * P /
          (Real.log P) ^ A := by
  let ε₀ : ℝ := min ε 1
  let S : ℕ := ⌈A⌉₊
  have hε₀ : 0 < ε₀ := by
    dsimp only [ε₀]
    exact lt_min hε zero_lt_one
  have hε₀le : ε₀ ≤ ε := by exact min_le_left _ _
  have hexp : 0 ≤ 3 / 2 - ε₀ := by
    have : ε₀ ≤ 1 := min_le_right _ _
    linarith
  have hAceil : A ≤ (S : ℝ) := by
    dsimp only [S]
    exact Nat.le_ceil A
  have hnatural :=
    eventually_specializedSmoothDiscrepancy_le_logSaving_of_analyticInputs'
      hPNT hVinogradov hK hε₀ S
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 hnatural
  have hlogOne : ∀ᶠ P : ℝ in atTop, 1 ≤ Real.log P :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have habsorb := eventually_log_rpow_le_self A
  filter_upwards [hlogOne, habsorb,
      eventually_ge_atTop (max (Q₀ : ℝ) 2)] with P hlogOneP habsorbP hPlarge
  intro I W N hImeas hconn hI hW hper hN
  let Q : ℕ := specializedRealScaleCeil P
  let J : Set ℝ := specializedRealScaleCore P I
  have hPtwo : 2 ≤ P := (le_max_right _ _).trans hPlarge
  have hPone : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hQtwo : 2 ≤ Q := two_le_specializedRealScaleCeil hPtwo
  have hQ₀le : Q₀ ≤ Q := by
    have : (Q₀ : ℝ) ≤ (Q : ℝ) :=
      (le_max_left _ _).trans hPlarge |>.trans (Nat.le_ceil P)
    exact_mod_cast this
  have hJmeas : MeasurableSet J := specializedRealScaleCore_measurable hImeas
  have hJconn : OrdConnected J := specializedRealScaleCore_ordConnected hconn
  have hJsubset : J ⊆ Set.Icc (Q : ℝ) (2 * (Q : ℝ)) := by
    exact specializedRealScaleCore_subset_dyadic hI
  have hNPε₀ : VinogradovParameterBound ε₀ K P N :=
    VinogradovParameterBound.mono_epsilon hK.le hlogOneP hε₀le hN
  have hNQ : VinogradovParameterBound ε₀ K (Q : ℝ) N :=
    VinogradovParameterBound.mono_scale hK.le hexp hPone (Nat.le_ceil P) hNPε₀
  have hcore := hQ₀ Q hQ₀le J W N hJmeas hJconn hJsubset hW hper hNQ
  have hsum := primeEquidistributionSum_eq_realScaleCore
    hPtwo hI W N N 2
  change primeEquidistributionSum P I W N N 2 =
    primeEquidistributionSum (Q : ℝ) J W N N 2 at hsum
  have hendpoint := norm_primeEquidistributionIntegral_sub_realScaleCore_le
    hPtwo hImeas hI W hW hper N N 2
  change ‖primeEquidistributionIntegral I W N N 2 -
      primeEquidistributionIntegral J W N N 2‖ ≤
    taoC3Norm W / Real.log P at hendpoint
  have hC3 : 0 ≤ taoC3Norm W := taoC3Norm_nonneg_of_smooth W hW hper
  have hmainScale := naturalCeil_logSaving_le_real_logSaving
    hPone hlogOneP hAceil
  change (Q : ℝ) / (Real.log (Q : ℝ)) ^ S ≤
    2 * P / (Real.log P) ^ A at hmainScale
  have hmain :
      specializedFourierReconstructionConstant * taoC3Norm W * (Q : ℝ) /
          (Real.log Q) ^ S ≤
        2 * specializedFourierReconstructionConstant * taoC3Norm W * P /
          (Real.log P) ^ A := by
    have hfactor : 0 ≤ specializedFourierReconstructionConstant * taoC3Norm W :=
      mul_nonneg specializedFourierReconstructionConstant_pos.le hC3
    calc
      specializedFourierReconstructionConstant * taoC3Norm W * (Q : ℝ) /
          (Real.log Q) ^ S =
        (specializedFourierReconstructionConstant * taoC3Norm W) *
          ((Q : ℝ) / (Real.log Q) ^ S) := by ring
      _ ≤ (specializedFourierReconstructionConstant * taoC3Norm W) *
          (2 * P / (Real.log P) ^ A) :=
        mul_le_mul_of_nonneg_left hmainScale hfactor
      _ = 2 * specializedFourierReconstructionConstant * taoC3Norm W * P /
          (Real.log P) ^ A := by ring
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogAPos : 0 < (Real.log P) ^ A := Real.rpow_pos_of_pos hlogP A
  have hendpointScale : taoC3Norm W / Real.log P ≤
      taoC3Norm W * P / (Real.log P) ^ A := by
    apply (div_le_div_iff₀ hlogP hlogAPos).2
    calc
      taoC3Norm W * (Real.log P) ^ A ≤ taoC3Norm W * P :=
        mul_le_mul_of_nonneg_left habsorbP hC3
      _ ≤ taoC3Norm W * P * Real.log P := by
        exact le_mul_of_one_le_right (mul_nonneg hC3 hPpos.le) hlogOneP
  calc
    ‖primeEquidistributionSum P I W N N 2 -
        primeEquidistributionIntegral I W N N 2‖ =
      ‖(primeEquidistributionSum (Q : ℝ) J W N N 2 -
          primeEquidistributionIntegral J W N N 2) +
        (primeEquidistributionIntegral J W N N 2 -
          primeEquidistributionIntegral I W N N 2)‖ := by
        rw [hsum]
        congr 1
        ring
    _ ≤ ‖primeEquidistributionSum (Q : ℝ) J W N N 2 -
          primeEquidistributionIntegral J W N N 2‖ +
        ‖primeEquidistributionIntegral J W N N 2 -
          primeEquidistributionIntegral I W N N 2‖ := norm_add_le _ _
    _ ≤ specializedFourierReconstructionConstant * taoC3Norm W * (Q : ℝ) /
          (Real.log Q) ^ S + taoC3Norm W / Real.log P :=
      add_le_add hcore (by simpa only [norm_sub_rev] using hendpoint)
    _ ≤ 2 * specializedFourierReconstructionConstant * taoC3Norm W * P /
          (Real.log P) ^ A + taoC3Norm W * P / (Real.log P) ^ A :=
      add_le_add hmain hendpointScale
    _ = specializedRealScaleReconstructionConstant * taoC3Norm W * P /
          (Real.log P) ^ A := by
      unfold specializedRealScaleReconstructionConstant
      ring

/-- Elementary uniform bound used to absorb the bounded real scales left
before the eventual analytic threshold. -/
theorem norm_specializedSmoothDiscrepancy_le_crude
    {P : ℝ} {I : Set ℝ} (hP : 2 ≤ P) (hImeas : MeasurableSet I)
    (hI : I ⊆ Set.Icc P (2 * P))
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hper : IsZ2Periodic W)
    (N : ℝ) :
    ‖primeEquidistributionSum P I W N N 2 -
        primeEquidistributionIntegral I W N N 2‖ ≤
      (2 * P + 1) * taoC3Norm W +
        (taoC3Norm W / Real.log P) * P := by
  let Z : ℝ × ℝ → ℂ := fun _ => 0
  have hC3 : 0 ≤ taoC3Norm W := taoC3Norm_nonneg_of_smooth W hW hper
  have hbdd : ∀ x : ℝ × ℝ, ‖W x‖ ≤ taoC3Norm W := fun x =>
    norm_le_taoC3Norm_of_bddAbove W
      (fun i _ => bddAbove_iteratedFDeriv_norm_range W hW hper i) x
  have happrox : ∀ x, ‖W x - Z x‖ ≤ taoC3Norm W := by
    intro x
    simpa only [Z, sub_zero] using hbdd x
  have hZcont : Continuous Z := continuous_const
  have hZerror :
      ‖primeEquidistributionSum P I Z N N 2 -
          primeEquidistributionIntegral I Z N N 2‖ ≤ 0 := by
    simp [Z, primeEquidistributionSum, primeEquidistributionIntegral]
  have hraw := norm_primeEquidistributionDiscrepancy_le_of_approx
    hP hImeas hI W Z hW.continuous hZcont N N 2 hC3 happrox hZerror
  simpa only [add_zero] using hraw

/-- The elementary bound on a compact scale range is a uniform multiple of
the requested logarithmic-saving normalization. -/
theorem boundedScaleCrude_le_real_logSaving
    {P B A C3 : ℝ} (hP : 2 ≤ P) (hPB : P ≤ B)
    (hA : 0 ≤ A) (hC3 : 0 ≤ C3) :
    (2 * P + 1) * C3 + (C3 / Real.log P) * P ≤
      ((2 * B + 1 + B / Real.log 2) * B ^ A) * C3 * P /
        (Real.log P) ^ A := by
  have hB : 2 ≤ B := hP.trans hPB
  have hPpos : 0 < P := by linarith
  have hBpos : 0 < B := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoP : Real.log 2 ≤ Real.log P :=
    Real.log_le_log (by norm_num) hP
  have hfirst : (2 * P + 1) * C3 ≤ (2 * B + 1) * C3 := by
    gcongr
  have hdiv : C3 / Real.log P ≤ C3 / Real.log 2 :=
    div_le_div_of_nonneg_left hC3 hlogTwo hlogTwoP
  have hsecond : (C3 / Real.log P) * P ≤
      (C3 / Real.log 2) * B := by
    exact mul_le_mul hdiv hPB (by positivity) (by positivity)
  let E : ℝ := 2 * B + 1 + B / Real.log 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hcrude :
      (2 * P + 1) * C3 + (C3 / Real.log P) * P ≤ E * C3 := by
    calc
      (2 * P + 1) * C3 + (C3 / Real.log P) * P ≤
          (2 * B + 1) * C3 + (C3 / Real.log 2) * B :=
        add_le_add hfirst hsecond
      _ = E * C3 := by dsimp only [E]; ring
  have hlogP_le_B : Real.log P ≤ B := by
    calc
      Real.log P ≤ P - 1 := Real.log_le_sub_one_of_pos hPpos
      _ ≤ P := by linarith
      _ ≤ B := hPB
  have hpow : (Real.log P) ^ A ≤ B ^ A :=
    Real.rpow_le_rpow hlogP.le hlogP_le_B hA
  have hlogAPos : 0 < (Real.log P) ^ A :=
    Real.rpow_pos_of_pos hlogP A
  refine hcrude.trans ?_
  apply (le_div_iff₀ hlogAPos).2
  calc
    E * C3 * (Real.log P) ^ A ≤ E * C3 * B ^ A :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hE hC3)
    _ ≤ E * C3 * B ^ A * P :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    _ = ((2 * B + 1 + B / Real.log 2) * B ^ A) * C3 * P := by
      dsimp only [E]
      ring

/-- Conditional closure of the literal specialized Theorem 2.5 contract.
The constant absorbs both the eventual real-scale Fourier estimate and the
bounded initial scales. -/
theorem taoTheorem25Specialized_of_analyticInputs
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate) :
    TaoTheorem25SpecializedConclusion := by
  intro ε hε A hA K hK
  have hlarge :=
    eventually_specializedSmoothDiscrepancy_le_real_logSaving_of_analyticInputs
      hPNT hVinogradov hK hε hA
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 hlarge
  let B : ℝ := max B₀ 2
  let E : ℝ := 2 * B + 1 + B / Real.log 2
  let Csmall : ℝ := E * B ^ A
  let C : ℝ := specializedRealScaleReconstructionConstant + Csmall
  have hB : 2 ≤ B := le_max_right _ _
  have hBpos : 0 < B := by linarith
  have hEpos : 0 < E := by
    dsimp only [E]
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hCsmall : 0 < Csmall := by
    dsimp only [Csmall]
    exact mul_pos hEpos (Real.rpow_pos_of_pos hBpos A)
  have hC : 0 < C := by
    dsimp only [C]
    linarith [specializedRealScaleReconstructionConstant_pos]
  refine ⟨C, hC, ?_⟩
  intro P I W N hP hImeas hconn hI hW hper hN
  have hC3 : 0 ≤ taoC3Norm W := taoC3Norm_nonneg_of_smooth W hW hper
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hnormal : 0 ≤ taoC3Norm W * P / (Real.log P) ^ A := by
    positivity
  by_cases hlargeP : B ≤ P
  · have hB₀P : B₀ ≤ P := (le_max_left _ _).trans hlargeP
    have hbound := hB₀ P hB₀P I W N hImeas hconn hI hW hper hN
    refine hbound.trans ?_
    calc
      specializedRealScaleReconstructionConstant * taoC3Norm W * P /
          (Real.log P) ^ A = specializedRealScaleReconstructionConstant *
          (taoC3Norm W * P / (Real.log P) ^ A) := by ring
      _ ≤ C * (taoC3Norm W * P / (Real.log P) ^ A) :=
        mul_le_mul_of_nonneg_right
          (by dsimp only [C]; linarith [hCsmall]) hnormal
      _ = C * taoC3Norm W * P / (Real.log P) ^ A := by ring
  · have hPB : P ≤ B := le_of_not_ge hlargeP
    have hcrude := norm_specializedSmoothDiscrepancy_le_crude
      hP hImeas hI W hW hper N
    have hsmall := boundedScaleCrude_le_real_logSaving
      hP hPB hA.le hC3
    refine (hcrude.trans hsmall).trans ?_
    calc
      ((2 * B + 1 + B / Real.log 2) * B ^ A) * taoC3Norm W * P /
          (Real.log P) ^ A =
        Csmall * (taoC3Norm W * P / (Real.log P) ^ A) := by
          dsimp only [Csmall, E]
          ring
      _ ≤ C * (taoC3Norm W * P / (Real.log P) ^ A) :=
        mul_le_mul_of_nonneg_right
          (by dsimp only [C];
              linarith [specializedRealScaleReconstructionConstant_pos])
          hnormal
      _ = C * taoC3Norm W * P / (Real.log P) ^ A := by ring

end

end Tao2026

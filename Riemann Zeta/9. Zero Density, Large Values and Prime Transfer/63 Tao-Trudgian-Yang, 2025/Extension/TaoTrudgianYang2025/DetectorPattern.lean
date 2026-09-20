import TaoTrudgianYang2025.ZeroEnergyTypeI
import GuthMaynard.ExtractSeparated
import GuthMaynard.ArithmeticCoefficients

/-!
# Type-I detector large-value patterns

This module normalizes the native fixed-line detector on its exact closed
dyadic support.  The added left-endpoint coefficient is zero, so the closed
support required by `LargeValuePattern` agrees exactly with the native
half-open detector polynomial.
-/

open Complex

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- The detector coefficient after extracting the common scale factor
`N^σ`.  This is the coefficient occurring in the source Type-I large-value
pattern. -/
def scaledDetectorLineCoeff (σ T : ℝ) (N n : ℕ) : ℂ :=
  (((N : ℝ) ^ σ : ℝ) : ℂ) * detectorLineCoeffs σ T n

/-- A positive finite normalization dominating every scaled detector
coefficient on the closed dyadic block.  Taking the maximum, rather than the
sum, preserves the source threshold exponent. -/
def detectorPatternNormalization (σ T : ℝ) (N : ℕ) : ℝ :=
  max 1 ((Finset.Icc N (2 * N)).sup' (by
      refine ⟨N, Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
      omega)
    fun n => ‖scaledDetectorLineCoeff σ T N n‖)

/-- Normalized detector coefficients on closed support.  The native detector
uses `(N,2N]`, so the coefficient at the newly adjoined left endpoint is
defined to be zero. -/
def normalizedDetectorPatternCoeff (σ T : ℝ) (N n : ℕ) : ℂ :=
  if n = N then 0 else
    (detectorPatternNormalization σ T N : ℂ)⁻¹ *
      scaledDetectorLineCoeff σ T N n

theorem detectorPatternNormalization_pos (σ T : ℝ) (N : ℕ) :
    0 < detectorPatternNormalization σ T N := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Uniform epsilon-power control of the scaled detector coefficients on a
dyadic block.  This consumes the native kernel proof of the classical divisor
bound, rather than assuming a coefficient estimate. -/
theorem exists_scaledDetectorLineCoeff_bound
    (σ ε : ℝ) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℝ) (N n : ℕ), 1 ≤ T → 0 < N →
        n ∈ Finset.Icc N (2 * N) →
        ‖scaledDetectorLineCoeff σ T N n‖ ≤
          C * ((2 * N : ℕ) : ℝ) ^ ε := by
  obtain ⟨C, hC, hCoeff⟩ :=
    uniformDetectorCoeffBound_of_divisorCount divisorCountBound_native ε hε
  refine ⟨C, hC, ?_⟩
  intro T N n hT hN hn
  have hnBounds := Finset.mem_Icc.mp hn
  have hnPos : 0 < n := hN.trans_le hnBounds.1
  have hNPow : (N : ℝ) ^ σ ≤ (n : ℝ) ^ σ := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg N) (by exact_mod_cast hnBounds.1) hσ
  have hnPowPos : 0 < (n : ℝ) ^ σ :=
    Real.rpow_pos_of_pos (by exact_mod_cast hnPos) σ
  have hratio : (N : ℝ) ^ σ * (n : ℝ) ^ (-σ) ≤ 1 := by
    rw [Real.rpow_neg (by exact_mod_cast hnPos.le), ← div_eq_mul_inv,
      div_le_one₀ hnPowPos]
    exact hNPow
  have hdetector := hCoeff n T hnPos hT
  have hnUpper : (n : ℝ) ^ ε ≤ ((2 * N : ℕ) : ℝ) ^ ε := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnBounds.2) hε.le
  unfold scaledDetectorLineCoeff detectorLineCoeffs
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) σ), norm_mul,
    Complex.norm_natCast_cpow_of_pos hnPos]
  simp only [Complex.ofReal_re, neg_re]
  calc
    (N : ℝ) ^ σ * (‖detectorCoeff n T‖ * (n : ℝ) ^ (-σ)) =
        ((N : ℝ) ^ σ * (n : ℝ) ^ (-σ)) * ‖detectorCoeff n T‖ := by ring
    _ ≤ 1 * ‖detectorCoeff n T‖ := by
      exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ ≤ C * (n : ℝ) ^ ε := by simpa using hdetector
    _ ≤ C * ((2 * N : ℕ) : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left hnUpper hC.le

/-- The exact coefficient normalizer has only an epsilon-power loss, uniformly
in the detector height and dyadic scale. -/
theorem exists_detectorPatternNormalization_bound
    (σ ε : ℝ) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℝ) (N : ℕ), 1 ≤ T → 0 < N →
        detectorPatternNormalization σ T N ≤
          max 1 (C * ((2 * N : ℕ) : ℝ) ^ ε) := by
  obtain ⟨C, hC, hscaled⟩ :=
    exists_scaledDetectorLineCoeff_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro T N hT hN
  unfold detectorPatternNormalization
  apply max_le
  · exact le_max_left _ _
  · rw [Finset.sup'_le_iff]
    intro n hn
    exact (hscaled T N n hT hN hn).trans (le_max_right _ _)

/-- Standard subpower form of the normalizer estimate. -/
theorem exists_detectorPatternNormalization_le_const_mul_rpow
    (σ ε : ℝ) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (T : ℝ) (N : ℕ), 1 ≤ T → 1 < N →
        detectorPatternNormalization σ T N ≤ C * (N : ℝ) ^ ε := by
  obtain ⟨D, hD, hnorm⟩ :=
    exists_detectorPatternNormalization_bound σ ε hσ hε
  let C := max 1 (D * (2 : ℝ) ^ ε)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro T N hT hN
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hNPowOne : (1 : ℝ) ≤ (N : ℝ) ^ ε :=
    Real.one_le_rpow hNOne hε.le
  apply (hnorm T N hT (by omega)).trans
  apply max_le
  · calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * (N : ℝ) ^ ε := mul_le_mul (le_max_left _ _)
        hNPowOne zero_le_one (by positivity)
  · rw [show ((2 * N : ℕ) : ℝ) = (2 : ℝ) * (N : ℝ) by norm_num,
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)]
    calc
      D * ((2 : ℝ) ^ ε * (N : ℝ) ^ ε) =
          (D * (2 : ℝ) ^ ε) * (N : ℝ) ^ ε := by ring
      _ ≤ C * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg N) ε)

/-- An epsilon-power upper bound for the normalizer gives the corresponding
explicit lower bound for the normalized detector threshold. -/
theorem detectorPatternThreshold_lower_of_normalization_le
    (σ T C ε : ℝ) (N : ℕ) (hT : 1 < T)
    (hnorm : detectorPatternNormalization σ T N ≤ C * (N : ℝ) ^ ε) :
    ((N : ℝ) ^ σ / (C * (N : ℝ) ^ ε)) * (1 / (4 * Real.log T)) ≤
      ((N : ℝ) ^ σ / detectorPatternNormalization σ T N) *
        (1 / (4 * Real.log T)) := by
  have hthreshold : 0 ≤ 1 / (4 * Real.log T) := by
    have : 0 < Real.log T := Real.log_pos hT
    positivity
  apply mul_le_mul_of_nonneg_right _ hthreshold
  exact div_le_div_of_nonneg_left
    (Real.rpow_nonneg (Nat.cast_nonneg N) σ)
    (detectorPatternNormalization_pos σ T N)
    hnorm

/-- The lower admissible detector-scale relation absorbs the logarithmic
height loss into an arbitrary positive power of the dyadic scale. -/
theorem log_height_le_admissible_scale_rpow
    (η T : ℝ) (N : ℕ) (hη : 0 < η) (hT : 1 ≤ T) (hN : 0 < N)
    (hscale : T ^ (1 / 100 : ℝ) ≤ (N : ℝ)) :
    Real.log T ≤ (η / 100)⁻¹ * (N : ℝ) ^ η := by
  let q : ℝ := η / 100
  have hq : 0 < q := div_pos hη (by norm_num)
  have hTNonneg : 0 ≤ T := le_trans (by norm_num) hT
  have hNNonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpow : T ^ q ≤ (N : ℝ) ^ η := by
    calc
      T ^ q = (T ^ (1 / 100 : ℝ)) ^ η := by
        rw [← Real.rpow_mul hTNonneg]
        congr 1
        dsimp [q]
        ring
      _ ≤ (N : ℝ) ^ η :=
        Real.rpow_le_rpow (Real.rpow_nonneg hTNonneg _) hscale hη.le
  calc
    Real.log T ≤ T ^ q / q := Real.log_le_rpow_div hTNonneg hq
    _ ≤ (N : ℝ) ^ η / q := div_le_div_of_nonneg_right hpow hq.le
    _ = q⁻¹ * (N : ℝ) ^ η := by field_simp

/-- Combined coefficient and logarithmic loss for the normalized Type-I
threshold.  Both losses are explicit powers of the admissible dyadic scale. -/
theorem detectorPatternThreshold_lower_admissible
    (σ η T C : ℝ) (N : ℕ) (hη : 0 < η) (hT : 1 < T)
    (hC : 0 < C) (hN : 0 < N)
    (hscale : T ^ (1 / 100 : ℝ) ≤ (N : ℝ))
    (hnorm : detectorPatternNormalization σ T N ≤ C * (N : ℝ) ^ η) :
    ((N : ℝ) ^ σ / (C * (N : ℝ) ^ η)) *
        (((η / 100) * (N : ℝ) ^ (-η)) / 4) ≤
      ((N : ℝ) ^ σ / detectorPatternNormalization σ T N) *
        (1 / (4 * Real.log T)) := by
  let q : ℝ := η / 100
  have hq : 0 < q := div_pos hη (by norm_num)
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLogPos : 0 < Real.log T := Real.log_pos hT
  have hLogBound : Real.log T ≤ q⁻¹ * (N : ℝ) ^ η := by
    simpa [q] using log_height_le_admissible_scale_rpow η T N hη hT.le hN hscale
  have hMajorPos : 0 < q⁻¹ * (N : ℝ) ^ η := by positivity
  have hInvLog : q * (N : ℝ) ^ (-η) ≤ 1 / Real.log T := by
    calc
      q * (N : ℝ) ^ (-η) = 1 / (q⁻¹ * (N : ℝ) ^ η) := by
        rw [Real.rpow_neg hNReal.le]
        field_simp
      _ ≤ 1 / Real.log T := one_div_le_one_div_of_le hLogPos hLogBound
  have hQuarter : (q * (N : ℝ) ^ (-η)) / 4 ≤
      1 / (4 * Real.log T) := by
    calc
      (q * (N : ℝ) ^ (-η)) / 4 ≤ (1 / Real.log T) / 4 := by
        exact div_le_div_of_nonneg_right hInvLog (by norm_num)
      _ = 1 / (4 * Real.log T) := by field_simp
  have hFactorNonneg : 0 ≤ (N : ℝ) ^ σ / (C * (N : ℝ) ^ η) := by
    positivity
  calc
    ((N : ℝ) ^ σ / (C * (N : ℝ) ^ η)) *
        (((η / 100) * (N : ℝ) ^ (-η)) / 4) =
        ((N : ℝ) ^ σ / (C * (N : ℝ) ^ η)) *
          ((q * (N : ℝ) ^ (-η)) / 4) := by rfl
    _ ≤ ((N : ℝ) ^ σ / (C * (N : ℝ) ^ η)) *
          (1 / (4 * Real.log T)) :=
      mul_le_mul_of_nonneg_left hQuarter hFactorNonneg
    _ ≤ ((N : ℝ) ^ σ / detectorPatternNormalization σ T N) *
          (1 / (4 * Real.log T)) :=
      detectorPatternThreshold_lower_of_normalization_le σ T C η N hT hnorm

theorem normalizedDetectorPatternCoeff_norm_le_one
    (σ T : ℝ) (N n : ℕ) (hn : n ∈ Finset.Icc N (2 * N)) :
    ‖normalizedDetectorPatternCoeff σ T N n‖ ≤ 1 := by
  by_cases hnN : n = N
  · simp [normalizedDetectorPatternCoeff, hnN]
  · rw [normalizedDetectorPatternCoeff, if_neg hnN, norm_mul,
      norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (detectorPatternNormalization_pos σ T N)]
    rw [inv_mul_le_one₀ (detectorPatternNormalization_pos σ T N)]
    exact (Finset.le_sup' (fun m => ‖scaledDetectorLineCoeff σ T N m‖) hn).trans
      (le_max_right _ _)

private theorem closedDyadic_eq_insert (N : ℕ) :
    Finset.Icc N (2 * N) = insert N (Finset.Ioc N (2 * N)) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
  omega

/-- The normalized closed-support phase sum is exactly the native detector
divided by its positive normalization. -/
theorem normalizedDetectorPattern_sum_eq
    (σ T t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc N (2 * N),
      normalizedDetectorPatternCoeff σ T N n * dirichletPhase n t) =
        ((((N : ℝ) ^ σ) / detectorPatternNormalization σ T N : ℝ) : ℂ) *
          detectPoly N (σ + I * t) T := by
  rw [closedDyadic_eq_insert]
  have hNnotmem : N ∉ Finset.Ioc N (2 * N) := by simp
  rw [Finset.sum_insert hNnotmem]
  simp only [normalizedDetectorPatternCoeff, if_pos, zero_mul, zero_add]
  rw [detectPoly_eq_dirichletPoly]
  unfold dirichletPoly dyadicInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≠ N := by
    rw [Finset.mem_Ioc] at hn
    omega
  rw [if_neg hnN]
  unfold scaledDetectorLineCoeff
  rw [div_eq_mul_inv]
  push_cast
  ring_nf
  unfold dirichletPhase
  congr 1
  apply congrArg (Complex.cpow (n : ℂ))
  ring

/-- Build an exact source `LargeValuePattern` from a finite one-separated set
of ordinates on which one fixed native Type-I detector is large. -/
def detectorLargeValuePattern
    (σ T threshold a b : ℝ) (N : ℕ) (W : Finset ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold)
    (hab : a < b) (hW : ∀ t ∈ W, a ≤ t ∧ t ≤ b)
    (hsep : IsOneSeparated W)
    (hlarge : ∀ t ∈ W, threshold ≤ ‖detectPoly N (σ + I * t) T‖) :
    LargeValuePattern where
  N := N
  scale := N
  T := b - a
  V := ((N : ℝ) ^ σ / detectorPatternNormalization σ T N) * threshold
  coeff := normalizedDetectorPatternCoeff σ T N
  indices := Finset.Icc N (2 * N)
  intervalLeft := a
  intervalRight := b
  ordinates := W
  N_eq_scale := rfl
  one_lt_N := by exact_mod_cast hN
  T_pos := sub_pos.mpr hab
  V_pos := mul_pos
    (div_pos (Real.rpow_pos_of_pos (by exact_mod_cast Nat.zero_lt_of_lt hN) σ)
      (detectorPatternNormalization_pos σ T N)) hthreshold
  mem_indices_iff := by
    intro n
    simp only [Finset.mem_Icc]
    norm_cast
  coeff_one_bounded := normalizedDetectorPatternCoeff_norm_le_one σ T N
  interval_length := rfl
  ordinates_in_interval := hW
  ordinates_oneSeparated := hsep
  large := by
    intro t ht
    rw [normalizedDetectorPattern_sum_eq σ T t N, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos
        (Real.rpow_pos_of_pos (by exact_mod_cast Nat.zero_lt_of_lt hN) σ)
        (detectorPatternNormalization_pos σ T N))]
    exact mul_le_mul_of_nonneg_left (hlarge t ht)
      (div_nonneg (Real.rpow_nonneg (by positivity) σ)
        (detectorPatternNormalization_pos σ T N).le)

/-- Indexed form of `detectorLargeValuePattern`.  One-separation makes the
ordinate map injective, so its image finset retains every index exactly. -/
def indexedDetectorLargeValuePattern
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ T threshold a b : ℝ) (N : ℕ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold)
    (hab : a < b) (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤ ‖detectPoly N (σ + I * W x) T‖) :
    LargeValuePattern :=
  detectorLargeValuePattern σ T threshold a b N
    (Finset.univ.image W) hN hthreshold hab
    (by
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨x, _, rfl⟩ := ht
      exact hW x)
    (image_isOneSeparated_of_indexed_oneSeparated W hsep)
    (by
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨x, _, rfl⟩ := ht
      exact hlarge x)

@[simp] theorem indexedDetectorLargeValuePattern_ordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ T threshold a b : ℝ) (N : ℕ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold)
    (hab : a < b) (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤ ‖detectPoly N (σ + I * W x) T‖) :
    (indexedDetectorLargeValuePattern σ T threshold a b N W hN
      hthreshold hab hW hsep hlarge).ordinates = Finset.univ.image W := rfl

/-- The packaged pattern's set energy is exactly the indexed energy; in
particular, the packaging step loses no multiplicity. -/
theorem indexedDetectorLargeValuePattern_energy_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ T threshold a b : ℝ) (N : ℕ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold)
    (hab : a < b) (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤ ‖detectPoly N (σ + I * W x) T‖) :
    finsetAdditiveEnergy
      (indexedDetectorLargeValuePattern σ T threshold a b N W hN
        hthreshold hab hW hsep hlarge).ordinates =
      approximateAdditiveEnergyOf 1 W := by
  rw [indexedDetectorLargeValuePattern_ordinates]
  exact finsetAdditiveEnergy_image_eq W hsep

/-- Every inhabited one-separated Type-I detector class is an actual source
`LargeValuePattern`.  Its ordinate energy is exactly the indexed class energy,
and all scale, interval, threshold, and normalization data remain explicit. -/
theorem exists_typeIDetectorClassPattern
    (δ σ T : ℝ) (hT : Real.exp 2 ≤ T)
    (shifted : TypeIZeroCopy σ T → ℝ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L)
    (label : TypeISeparatedScaleColor T L)
    (x₀ : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label)
    (hshift : ∀ x : TypeIZeroCopy σ T,
      |(x.1.1 : ℂ).im - shifted x| ≤ T ^ δ)
    (hlarge : ∀ x : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label,
      1 / (4 * Real.log T) ≤
        ‖detectPoly (2 ^ typeIScaleColorIndex label.1)
          (σ + I * shifted x.1) T‖)
    (hsep : ∀ x y : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label,
      x ≠ y → 1 ≤ |shifted x.1 - shifted y.1|) :
    ∃ P : LargeValuePattern,
      P.N = ((2 ^ typeIScaleColorIndex label.1 : ℕ) : ℝ) ∧
      P.scale = 2 ^ typeIScaleColorIndex label.1 ∧
      P.T = (2 * T + T ^ δ) - (T - T ^ δ) ∧
      P.V = (((2 ^ typeIScaleColorIndex label.1 : ℕ) : ℝ) ^ σ /
          detectorPatternNormalization σ T
            (2 ^ typeIScaleColorIndex label.1)) *
        (1 / (4 * Real.log T)) ∧
      P.ordinates = Finset.univ.image
        (fun x : EnergyColorFiber
          (typeISeparatedScaleColor σ T shifted L hlocal) label => shifted x.1) ∧
      finsetAdditiveEnergy P.ordinates =
        approximateAdditiveEnergyOf 1
          (fun x : EnergyColorFiber
            (typeISeparatedScaleColor σ T shifted L hlocal) label => shifted x.1) := by
  classical
  let color := typeISeparatedScaleColor σ T shifted L hlocal
  let W : EnergyColorFiber color label → ℝ := fun x => shifted x.1
  let j := typeIScaleColorIndex label.1
  let N := 2 ^ j
  have hjMem : j ∈ admissibleDyadicIndices T := by
    exact typeISeparatedScaleColor_index_mem σ T shifted L hlocal label x₀
  have hjAdmissible : IsAdmissibleDyadicScale T j :=
    (mem_admissibleDyadicIndices T j).mp hjMem
  have hExp : 1 < Real.exp 2 := by
    rw [← Real.exp_zero]
    exact Real.exp_strictMono (by norm_num)
  have hTOne : 1 < T := hExp.trans_le hT
  have hNReal : 1 < (N : ℝ) := by
    have hPow : 1 < (2 : ℝ) ^ j :=
      (Real.one_lt_rpow hTOne
        (show (0 : ℝ) < 1 / 100 by norm_num)).trans_le hjAdmissible.1
    dsimp [N]
    exact_mod_cast hPow
  have hN : 1 < N := by exact_mod_cast hNReal
  have hthreshold : 0 < 1 / (4 * Real.log T) := by
    have hlog : 0 < Real.log T := Real.log_pos hTOne
    positivity
  have hTPos : 0 < T := zero_lt_one.trans hTOne
  have hpowNonneg : 0 ≤ T ^ δ := Real.rpow_nonneg hTPos.le δ
  have hab : T - T ^ δ < 2 * T + T ^ δ := by linarith
  have hW : ∀ x : EnergyColorFiber color label,
      T - T ^ δ ≤ W x ∧ W x ≤ 2 * T + T ^ δ := by
    intro x
    have hZeroMem : (x.1.1.1 : ℂ) ∈ zerosInRect σ 1 T (2 * T) :=
      (Finset.mem_filter.mp x.1.1.2).1
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hZeroMem
    have hRect := hZeroMem.1
    rw [mem_ZeroRectangle] at hRect
    have hDisplacement := hshift x.1
    rw [abs_le] at hDisplacement
    change T - T ^ δ ≤ shifted x.1 ∧ shifted x.1 ≤ 2 * T + T ^ δ
    constructor <;> linarith
  have hlargeW : ∀ x : EnergyColorFiber color label,
      1 / (4 * Real.log T) ≤ ‖detectPoly N (σ + I * W x) T‖ := by
    intro x
    exact hlarge x
  have hsepW : ∀ x y : EnergyColorFiber color label,
      x ≠ y → 1 ≤ |W x - W y| := hsep
  let P := indexedDetectorLargeValuePattern σ T (1 / (4 * Real.log T))
    (T - T ^ δ) (2 * T + T ^ δ) N W hN hthreshold hab hW hsepW hlargeW
  refine ⟨P, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact indexedDetectorLargeValuePattern_energy_eq σ T
    (1 / (4 * Real.log T)) (T - T ^ δ) (2 * T + T ^ δ)
    N W hN hthreshold hab hW hsepW hlargeW

/-- Empty detector classes contribute zero energy; every nonempty class is
represented exactly by a source `LargeValuePattern`.  This is the form used
when summing the four color classes. -/
theorem typeIDetectorClass_energy_eq_zero_or_exists_pattern
    (δ σ T : ℝ) (hT : Real.exp 2 ≤ T)
    (shifted : TypeIZeroCopy σ T → ℝ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L)
    (label : TypeISeparatedScaleColor T L)
    (hshift : ∀ x : TypeIZeroCopy σ T,
      |(x.1.1 : ℂ).im - shifted x| ≤ T ^ δ)
    (hlarge : ∀ x : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label,
      1 / (4 * Real.log T) ≤
        ‖detectPoly (2 ^ typeIScaleColorIndex label.1)
          (σ + I * shifted x.1) T‖)
    (hsep : ∀ x y : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label,
      x ≠ y → 1 ≤ |shifted x.1 - shifted y.1|) :
    approximateAdditiveEnergyOf 1
        (fun x : EnergyColorFiber
          (typeISeparatedScaleColor σ T shifted L hlocal) label => shifted x.1) = 0 ∨
      ∃ P : LargeValuePattern,
        finsetAdditiveEnergy P.ordinates =
          approximateAdditiveEnergyOf 1
            (fun x : EnergyColorFiber
              (typeISeparatedScaleColor σ T shifted L hlocal) label => shifted x.1) ∧
        P.N = ((2 ^ typeIScaleColorIndex label.1 : ℕ) : ℝ) ∧
        P.scale = 2 ^ typeIScaleColorIndex label.1 ∧
        P.T = (2 * T + T ^ δ) - (T - T ^ δ) ∧
        P.V = (((2 ^ typeIScaleColorIndex label.1 : ℕ) : ℝ) ^ σ /
            detectorPatternNormalization σ T
              (2 ^ typeIScaleColorIndex label.1)) *
          (1 / (4 * Real.log T)) := by
  classical
  let color := typeISeparatedScaleColor σ T shifted L hlocal
  let W : EnergyColorFiber color label → ℝ := fun x => shifted x.1
  cases isEmpty_or_nonempty (EnergyColorFiber color label) with
  | inl hempty =>
      left
      simp [approximateAdditiveEnergyOf]
  | inr hnonempty =>
      right
      let x₀ : EnergyColorFiber color label := Classical.choice hnonempty
      obtain ⟨P, hPN, hPscale, hPT, hPV, hPordinates, henergy⟩ :=
        exists_typeIDetectorClassPattern δ σ T hT shifted L hlocal label x₀
          hshift hlarge hsep
      refine ⟨P, ?_, hPN, hPscale, hPT, hPV⟩
      exact henergy

end TaoTrudgianYang2025

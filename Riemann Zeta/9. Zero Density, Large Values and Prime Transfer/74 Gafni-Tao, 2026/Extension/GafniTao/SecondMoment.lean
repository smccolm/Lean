import GafniTao.LocalZeroCount
import GafniTao.FourierBump
import GafniTao.ZeroSumSup
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Gafni--Tao second-moment zero kernel

This file implements the finite Schur estimate in Lemma 2.3.  It keeps the
actual analytic multiplicities and the literal tenfold ordinate-decay kernel.
-/

open Asymptotics Complex Finset Filter Set
open scoped BigOperators ContDiff FourierTransform

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- The literal positive decay kernel appearing after the Fourier expansion
in Lemma 2.3. -/
noncomputable def zeroPairDecay (rho rho' : ℂ) : ℝ :=
  1 / (1 + |rho.im - rho'.im|) ^ (10 : ℕ)

/-- A summable half-integer majorant for the ordinate-bin decomposition.  The
half shift prevents a singular term at the central bin. -/
noncomputable def integerBinDecay (n : ℤ) : ℝ :=
  1 / |(n : ℝ) + 1 / 2| ^ (10 : ℕ)

theorem summable_integerBinDecay : Summable integerBinDecay := by
  change Summable (fun n : ℤ => 1 / |(n : ℝ) + 1 / 2| ^ (10 : ℕ))
  have h := (Real.summable_one_div_int_add_rpow (1 / 2) 10).mpr (by norm_num)
  exact h.congr (fun n => congrArg (fun q : ℝ => 1 / q)
    (Real.rpow_natCast |(n : ℝ) + 1 / 2| 10))

/-- The fixed, finite Schur constant for the tenfold kernel. -/
noncomputable def integerBinDecayMass : ℝ :=
  ∑' n : ℤ, integerBinDecay n

theorem integerBinDecay_nonneg (n : ℤ) : 0 ≤ integerBinDecay n := by
  unfold integerBinDecay
  positivity

theorem integerBinDecayMass_nonneg : 0 ≤ integerBinDecayMass := by
  unfold integerBinDecayMass
  exact tsum_nonneg integerBinDecay_nonneg

private theorem halfInteger_abs_pos (n : ℤ) :
    0 < |(n : ℝ) + 1 / 2| := by
  rw [abs_pos]
  intro hn
  have htwo : (2 : ℝ) * n + 1 = 0 := by linarith
  have hcast : ((2 * n + 1 : ℤ) : ℝ) = 0 := by
    norm_num at htwo ⊢
    exact htwo
  have hint : 2 * n + 1 = 0 := by exact_mod_cast hcast
  omega

/-- Passing to integer ordinate bins loses only the explicit factor `3^10`.
This is the pointwise kernel comparison used in the Schur row sum. -/
theorem zeroPairDecay_le_integerBinDecay (rho rho' : ℂ) :
    zeroPairDecay rho rho' ≤
      3 ^ (10 : ℕ) * integerBinDecay (⌊rho'.im⌋ - ⌊rho.im⌋) := by
  let a : ℝ := (⌊rho.im⌋ : ℤ)
  let b : ℝ := (⌊rho'.im⌋ : ℤ)
  have haLower : a ≤ rho.im := by exact Int.floor_le rho.im
  have haUpper : rho.im < a + 1 := by exact Int.lt_floor_add_one rho.im
  have hbLower : b ≤ rho'.im := by exact Int.floor_le rho'.im
  have hbUpper : rho'.im < b + 1 := by exact Int.lt_floor_add_one rho'.im
  have hba : |b - rho'.im| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hta : |rho.im - a| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hshift :
      |b - a + 1 / 2| ≤ 3 * (1 + |rho.im - rho'.im|) := by
    have heq : b - a + 1 / 2 =
        (b - rho'.im) + (rho'.im - rho.im) + (rho.im - a) + 1 / 2 := by ring
    rw [heq]
    calc
      |(b - rho'.im) + (rho'.im - rho.im) + (rho.im - a) + 1 / 2|
          ≤ |(b - rho'.im) + (rho'.im - rho.im) + (rho.im - a)| +
              |(1 / 2 : ℝ)| := abs_add_le _ _
      _ ≤ (|(b - rho'.im) + (rho'.im - rho.im)| + |rho.im - a|) +
              |(1 / 2 : ℝ)| := by
            have hxy := abs_add_le
              ((b - rho'.im) + (rho'.im - rho.im)) (rho.im - a)
            nlinarith
      _ ≤ ((|b - rho'.im| + |rho'.im - rho.im|) + |rho.im - a|) +
              |(1 / 2 : ℝ)| := by
            have hxy := abs_add_le (b - rho'.im) (rho'.im - rho.im)
            nlinarith
      _ ≤ 1 + |rho.im - rho'.im| + 1 + 1 / 2 := by
        rw [abs_sub_comm rho'.im rho.im, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        gcongr
      _ ≤ 3 * (1 + |rho.im - rho'.im|) := by
        have habs : 0 ≤ |rho.im - rho'.im| := abs_nonneg _
        linarith
  have hbase : 0 < 1 + |rho.im - rho'.im| := by positivity
  have hhalf : 0 < |(((⌊rho'.im⌋ - ⌊rho.im⌋ : ℤ) : ℝ)) + 1 / 2| :=
    halfInteger_abs_pos _
  have hcast :
      (((⌊rho'.im⌋ - ⌊rho.im⌋ : ℤ) : ℝ)) = b - a := by
    simp [a, b]
  have hpow :
      |(((⌊rho'.im⌋ - ⌊rho.im⌋ : ℤ) : ℝ)) + 1 / 2| ^ (10 : ℕ) ≤
        (3 * (1 + |rho.im - rho'.im|)) ^ (10 : ℕ) := by
    rw [hcast]
    gcongr
  unfold zeroPairDecay integerBinDecay
  rw [mul_one_div]
  rw [div_le_div_iff₀ (pow_pos hbase 10) (pow_pos hhalf 10)]
  calc
    1 * |(((⌊rho'.im⌋ - ⌊rho.im⌋ : ℤ) : ℝ)) + 1 / 2| ^ (10 : ℕ)
        ≤ (3 * (1 + |rho.im - rho'.im|)) ^ (10 : ℕ) := by simpa using hpow
    _ = 3 ^ (10 : ℕ) * (1 + |rho.im - rho'.im|) ^ (10 : ℕ) := by rw [mul_pow]

/-- Integer translation does not change the total half-integer decay mass. -/
theorem tsum_integerBinDecay_sub (a : ℤ) :
    (∑' z : ℤ, integerBinDecay (z - a)) = integerBinDecayMass := by
  unfold integerBinDecayMass
  simpa using (Equiv.subRight a).tsum_eq integerBinDecay

/-- The integer ordinate bin assigned by the floor convention. -/
noncomputable def ordinateBin (rho : ℂ) : ℤ := ⌊rho.im⌋

theorem floorFiber_subset_zeroLocalUnitBin
    {sigma T : ℝ} (z : ℤ) :
    (zeroSet sigma T).filter (fun rho => ordinateBin rho = z) ⊆
      zeroLocalUnitBin sigma T z := by
  intro rho hrho
  rw [Finset.mem_filter] at hrho
  rw [zeroLocalUnitBin, Finset.mem_filter]
  refine ⟨hrho.1, ?_⟩
  have hFloorLe : ((⌊rho.im⌋ : ℤ) : ℝ) ≤ rho.im := Int.floor_le rho.im
  have hLtFloor : rho.im < ((⌊rho.im⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one rho.im
  change (z : ℝ) ≤ rho.im ∧ rho.im < (z : ℝ) + 1
  rw [← hrho.2]
  exact And.intro hFloorLe hLtFloor

theorem floorFiber_multiplicity_le_log
    (sigma T : ℝ) (z : ℤ)
    (hsigmaLower : 0 ≤ sigma)
    (hT : max (Real.exp 2) 8 ≤ T) :
    ((∑ rho ∈ (zeroSet sigma T).filter (fun w => ordinateBin w = z),
        zeroMultiplicity rho : ℕ) : ℝ) ≤
      globalLocalZeroLogConstant * Real.log T := by
  have hNat :
      ∑ rho ∈ (zeroSet sigma T).filter (fun w => ordinateBin w = z),
          zeroMultiplicity rho ≤
        ∑ rho ∈ zeroLocalUnitBin sigma T z, zeroMultiplicity rho := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact floorFiber_subset_zeroLocalUnitBin z
    · intro rho _ _
      exact Nat.zero_le _
  have hReal :
      ((∑ rho ∈ (zeroSet sigma T).filter (fun w => ordinateBin w = z),
          zeroMultiplicity rho : ℕ) : ℝ) ≤
        ((∑ rho ∈ zeroLocalUnitBin sigma T z,
          zeroMultiplicity rho : ℕ) : ℝ) := by
    exact_mod_cast hNat
  exact hReal.trans (by
    simpa only using zeroLocalUnitBin_multiplicity_le_global_log
      sigma T z hsigmaLower hT)

/-- The exact Schur row estimate behind Gafni--Tao Lemma 2.3.  The sum is
over the actual symmetric zero set and carries analytic multiplicity. -/
theorem zeroPairDecay_row_sum_le
    (sigma T : ℝ) (rho : ℂ)
    (hsigmaLower : 0 ≤ sigma)
    (hT : max (Real.exp 2) 8 ≤ T) :
    ∑ rho' ∈ zeroSet sigma T,
        (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho' ≤
      (3 ^ (10 : ℕ) * integerBinDecayMass) *
        (globalLocalZeroLogConstant * Real.log T) := by
  let S := zeroSet sigma T
  let bins : Finset ℤ := S.image ordinateBin
  let a : ℤ := ordinateBin rho
  let mult : ℂ → ℝ := fun w => (zeroMultiplicity w : ℝ)
  let term : ℂ → ℝ := fun w => mult w * zeroPairDecay rho w
  have hAll : S.filter (fun w => ordinateBin w ∈ bins) = S := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S bins ordinateBin term
  rw [hAll] at hFiber
  have hLogNonneg : 0 ≤ Real.log T := by
    have hTExp : Real.exp 2 ≤ T := le_trans (le_max_left _ _) hT
    have hExpOne : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact Real.log_nonneg (hExpOne.le.trans hTExp)
  have hCLNonneg : 0 ≤ globalLocalZeroLogConstant * Real.log T :=
    mul_nonneg globalLocalZeroLogConstant_pos.le hLogNonneg
  have hEach : ∀ z ∈ bins,
      ∑ w ∈ S.filter (fun v => ordinateBin v = z), term w ≤
        (3 ^ (10 : ℕ) * integerBinDecay (z - a)) *
          (globalLocalZeroLogConstant * Real.log T) := by
    intro z _hz
    calc
      ∑ w ∈ S.filter (fun v => ordinateBin v = z), term w
          ≤ ∑ w ∈ S.filter (fun v => ordinateBin v = z),
              mult w * (3 ^ (10 : ℕ) * integerBinDecay (z - a)) := by
            apply Finset.sum_le_sum
            intro w hw
            rw [Finset.mem_filter] at hw
            unfold term
            apply mul_le_mul_of_nonneg_left
            · have hKernel := zeroPairDecay_le_integerBinDecay rho w
              change zeroPairDecay rho w ≤
                3 ^ (10 : ℕ) * integerBinDecay
                  (ordinateBin w - ordinateBin rho) at hKernel
              rw [hw.2] at hKernel
              simpa [a] using hKernel
            · unfold mult
              positivity
      _ = (3 ^ (10 : ℕ) * integerBinDecay (z - a)) *
            ((∑ w ∈ S.filter (fun v => ordinateBin v = z),
              zeroMultiplicity w : ℕ) : ℝ) := by
            simp only [mult, Nat.cast_sum]
            rw [← Finset.sum_mul]
            ring
      _ ≤ (3 ^ (10 : ℕ) * integerBinDecay (z - a)) *
            (globalLocalZeroLogConstant * Real.log T) := by
            apply mul_le_mul_of_nonneg_left
            · simpa [S] using floorFiber_multiplicity_le_log
                sigma T z hsigmaLower hT
            · exact mul_nonneg (by positivity) (integerBinDecay_nonneg _)
  calc
    ∑ rho' ∈ zeroSet sigma T,
        (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho'
        = ∑ w ∈ S, term w := by rfl
    _ = ∑ z ∈ bins, ∑ w ∈ S.filter (fun v => ordinateBin v = z), term w :=
      hFiber.symm
    _ ≤ ∑ z ∈ bins,
        (3 ^ (10 : ℕ) * integerBinDecay (z - a)) *
          (globalLocalZeroLogConstant * Real.log T) := Finset.sum_le_sum hEach
    _ = (3 ^ (10 : ℕ) *
          (∑ z ∈ bins, integerBinDecay (z - a))) *
          (globalLocalZeroLogConstant * Real.log T) := by
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
    _ ≤ (3 ^ (10 : ℕ) * integerBinDecayMass) *
          (globalLocalZeroLogConstant * Real.log T) := by
        apply mul_le_mul_of_nonneg_right _ hCLNonneg
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hSummable : Summable (fun z : ℤ => integerBinDecay (z - a)) := by
          exact summable_integerBinDecay.comp_injective (Equiv.subRight a).injective
        exact (hSummable.sum_le_tsum bins (fun z _ => integerBinDecay_nonneg _)).trans_eq
          (tsum_integerBinDecay_sub a)

/-- The full multiplicity-weighted double decay sum from Lemma 2.3. -/
noncomputable def zeroPairDecaySum (sigma T : ℝ) : ℝ :=
  ∑ rho ∈ zeroSet sigma T, (zeroMultiplicity rho : ℝ) *
    ∑ rho' ∈ zeroSet sigma T,
      (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho'

/-- Schur's test in the exact finite, multiplicity-weighted form used by the
paper. -/
theorem zeroPairDecaySum_le
    (sigma T : ℝ) (hsigmaLower : 0 ≤ sigma)
    (hT : max (Real.exp 2) 8 ≤ T) :
    zeroPairDecaySum sigma T ≤
      ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
        (Real.log T * (zeroCount sigma T : ℝ)) := by
  have hRow := fun rho => zeroPairDecay_row_sum_le sigma T rho hsigmaLower hT
  have hLogNonneg : 0 ≤ Real.log T := by
    have hTExp : Real.exp 2 ≤ T := le_trans (le_max_left _ _) hT
    exact Real.log_nonneg ((Real.one_lt_exp_iff.mpr (by norm_num)).le.trans hTExp)
  unfold zeroPairDecaySum
  calc
    ∑ rho ∈ zeroSet sigma T, (zeroMultiplicity rho : ℝ) *
        ∑ rho' ∈ zeroSet sigma T,
          (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho'
        ≤ ∑ rho ∈ zeroSet sigma T, (zeroMultiplicity rho : ℝ) *
            ((3 ^ (10 : ℕ) * integerBinDecayMass) *
              (globalLocalZeroLogConstant * Real.log T)) := by
          apply Finset.sum_le_sum
          intro rho hrho
          exact mul_le_mul_of_nonneg_left (hRow rho) (by positivity)
    _ = ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log T * (zeroCount sigma T : ℝ)) := by
        rw [← Finset.sum_mul]
        rw [← Nat.cast_sum]
        rw [← zeroCount_eq_weighted_sum]
        ring

/-- A compact parameter cutoff equal to one for every possible sum of two
critical-strip real parts. -/
noncomputable def spectralParameterBump
    (cutoff : GMSmoothCutoff) (s : ℝ) : ℝ :=
  cutoff (6 / 5 + 3 * s / 10)

theorem spectralParameterBump_eq_one
    (cutoff : GMSmoothCutoff) {s : ℝ} (hs : s ∈ Set.Icc 0 2) :
    spectralParameterBump cutoff s = 1 := by
  apply cutoff.equals_one
  rw [Set.mem_Icc] at hs ⊢
  constructor <;> linarith

theorem contDiff_spectralParameterBump (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (spectralParameterBump cutoff) := by
  exact cutoff.smooth.comp
    (contDiff_const.add ((contDiff_const.mul contDiff_id).div_const 10))

theorem support_spectralParameterBump (cutoff : GMSmoothCutoff) :
    Function.support (spectralParameterBump cutoff) ⊆
      Set.Icc (-2 / 3) (8 / 3) := by
  intro s hs
  have hrange := cutoff.support (by
    simpa only [spectralParameterBump, Function.mem_support] using hs)
  rw [Set.mem_Icc] at hrange ⊢
  constructor <;> linarith

/-- Compact two-variable family whose Fourier transform is the paper's
complexified bump transform for `0 ≤ s ≤ 2`. -/
noncomputable def complexifiedBumpFamily
    (cutoff : GMSmoothCutoff) (s u : ℝ) : ℂ :=
  (spectralParameterBump cutoff s : ℂ) *
    logScaleBumpComplex cutoff u *
      Complex.exp (((s * u : ℝ) : ℂ))

theorem contDiff_uncurry_complexifiedBumpFamily (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (Function.uncurry (complexifiedBumpFamily cutoff)) := by
  have hsReal : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => spectralParameterBump cutoff p.1) :=
    (contDiff_spectralParameterBump cutoff).comp contDiff_fst
  have hs : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => (spectralParameterBump cutoff p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsReal
  have hu : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => logScaleBumpComplex cutoff p.2) :=
    (contDiff_logScaleBumpComplex cutoff).comp contDiff_snd
  have hsuReal : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  have hsu : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((p.1 * p.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsuReal
  have hexp : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => Complex.exp (((p.1 * p.2 : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp hsu
  exact (hs.mul hu).mul hexp

theorem support_uncurry_complexifiedBumpFamily (cutoff : GMSmoothCutoff) :
    Function.support (Function.uncurry (complexifiedBumpFamily cutoff)) ⊆
      Set.Icc (-2 / 3) (8 / 3) ×ˢ Set.Icc (-2 / 5) (8 / 5) := by
  intro p hp
  rw [Function.mem_support] at hp
  constructor
  · apply support_spectralParameterBump cutoff
    rw [Function.mem_support]
    intro hzero
    apply hp
    change complexifiedBumpFamily cutoff p.1 p.2 = 0
    unfold complexifiedBumpFamily
    rw [hzero]
    simp
  · apply support_logScaleBumpComplex cutoff
    rw [Function.mem_support]
    intro hzero
    apply hp
    change complexifiedBumpFamily cutoff p.1 p.2 = 0
    unfold complexifiedBumpFamily
    rw [hzero]
    simp

/-- Uniform tenfold Fourier decay for the whole compactified vertical
parameter family. -/
theorem exists_complexifiedBumpFamily_tenfold_decay
    (cutoff : GMSmoothCutoff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s xi : ℝ,
      (1 + |xi|) ^ 10 *
          ‖𝓕 (fun u : ℝ => complexifiedBumpFamily cutoff s u) xi‖ ≤ K := by
  let F := complexifiedBumpFamily cutoff
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    contDiff_uncurry_complexifiedBumpFamily cutoff
  have hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc (-2 / 3) (8 / 3) ×ˢ Set.Icc (-2 / 5) (8 / 5) :=
    support_uncurry_complexifiedBumpFamily cutoff
  obtain ⟨K0, hK0, hZero⟩ :=
    exists_uniform_fourier_decay_of_rectangular_support
      hF (by norm_num : (-2 / 5 : ℝ) ≤ 8 / 5) hSupport 0
  obtain ⟨K10, hK10, hTen⟩ :=
    exists_uniform_fourier_decay_of_rectangular_support
      hF (by norm_num : (-2 / 5 : ℝ) ≤ 8 / 5) hSupport 10
  refine ⟨2 ^ (10 : ℕ) * (K0 + K10), by positivity, ?_⟩
  intro s xi
  by_cases hxi : |xi| ≤ 1
  · have hWeight : (1 + |xi|) ^ 10 ≤ 2 ^ (10 : ℕ) := by
      have hbase : 1 + |xi| ≤ 2 := by linarith
      gcongr
    have h0 := hZero s xi
    simp only [pow_zero, one_mul] at h0
    calc
      (1 + |xi|) ^ 10 * ‖𝓕 (fun u : ℝ => F s u) xi‖
          ≤ 2 ^ (10 : ℕ) * K0 :=
        mul_le_mul hWeight h0 (norm_nonneg _) (by positivity)
      _ ≤ 2 ^ (10 : ℕ) * (K0 + K10) := by
        gcongr
        exact le_add_of_nonneg_right hK10
  · have hone : 1 ≤ |xi| := le_of_lt (lt_of_not_ge hxi)
    have hWeight : (1 + |xi|) ^ 10 ≤
        2 ^ (10 : ℕ) * |xi| ^ 10 := by
      have hbase : 1 + |xi| ≤ 2 * |xi| := by linarith
      calc
        (1 + |xi|) ^ 10 ≤ (2 * |xi|) ^ 10 := by gcongr
        _ = 2 ^ (10 : ℕ) * |xi| ^ 10 := by rw [mul_pow]
    have h10 := hTen s xi
    calc
      (1 + |xi|) ^ 10 * ‖𝓕 (fun u : ℝ => F s u) xi‖
          ≤ (2 ^ (10 : ℕ) * |xi| ^ 10) *
              ‖𝓕 (fun u : ℝ => F s u) xi‖ :=
        mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
      _ = 2 ^ (10 : ℕ) *
          (|xi| ^ 10 * ‖𝓕 (fun u : ℝ => F s u) xi‖) := by ring
      _ ≤ 2 ^ (10 : ℕ) * K10 := by gcongr
      _ ≤ 2 ^ (10 : ℕ) * (K0 + K10) := by
        gcongr
        exact le_add_of_nonneg_left hK0

/-- The paper's complexified Fourier transform, with its literal phase
`exp (i u xi)` rather than Mathlib's normalized real-frequency phase. -/
noncomputable def complexifiedLogScaleBumpFourier
    (cutoff : GMSmoothCutoff) (xi : ℂ) : ℂ :=
  ∫ u : ℝ, logScaleBumpComplex cutoff u *
    Complex.exp (I * (u : ℂ) * xi)

/-- Exact normalization bridge from the source complex frequency to
Mathlib's Fourier transform. -/
theorem complexifiedLogScaleBumpFourier_eq_family_fourier
    (cutoff : GMSmoothCutoff) {s : ℝ} (hs : s ∈ Set.Icc 0 2) (d : ℝ) :
    complexifiedLogScaleBumpFourier cutoff ((d : ℂ) - I * (s : ℂ)) =
      𝓕 (fun u : ℝ => complexifiedBumpFamily cutoff s u)
        (-d / (2 * Real.pi)) := by
  unfold complexifiedLogScaleBumpFourier
  rw [Real.fourier_eq']
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  unfold complexifiedBumpFamily
  rw [spectralParameterBump_eq_one cutoff hs]
  simp only [Complex.ofReal_one, one_mul, smul_eq_mul]
  have hReorder : Complex.exp
        (((-2 * Real.pi * inner ℝ u (-d / (2 * Real.pi)) : ℝ) : ℂ) * I) *
          (logScaleBumpComplex cutoff u * Complex.exp (((s * u : ℝ) : ℂ))) =
      logScaleBumpComplex cutoff u *
        (Complex.exp
          (((-2 * Real.pi * inner ℝ u (-d / (2 * Real.pi)) : ℝ) : ℂ) * I) *
          Complex.exp (((s * u : ℝ) : ℂ))) := by ring
  rw [hReorder]
  rw [← Complex.exp_add]
  apply congrArg (fun q : ℂ => logScaleBumpComplex cutoff u * q)
  congr 1
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hfreq :
      -2 * Real.pi * inner ℝ u (-d / (2 * Real.pi)) = u * d := by
    rw [RCLike.inner_apply]
    simp only [starRingEnd_apply, star_trivial]
    field_simp [hpi]
  rw [hfreq]
  push_cast
  calc
    I * (u : ℂ) * ((d : ℂ) - I * (s : ℂ)) =
        (u : ℂ) * (d : ℂ) * I - (I * I) * ((u : ℂ) * (s : ℂ)) := by ring
    _ = (u : ℂ) * (d : ℂ) * I + (s : ℂ) * (u : ℂ) := by
      rw [Complex.I_mul_I]
      ring

/-- Uniform source-normalized decay on the full real-part range needed for
pairs of critical-strip zeros. -/
theorem exists_complexifiedLogScaleBumpFourier_tenfold_decay
    (cutoff : GMSmoothCutoff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K := by
  obtain ⟨K, hK, hDecay⟩ := exists_complexifiedBumpFamily_tenfold_decay cutoff
  let R : ℝ := 1 + 2 * Real.pi
  refine ⟨R ^ (10 : ℕ) * K, mul_nonneg (by positivity) hK, ?_⟩
  intro s hs d
  rw [complexifiedLogScaleBumpFourier_eq_family_fourier cutoff hs d]
  let xi : ℝ := -d / (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hd : |d| = (2 * Real.pi) * |xi| := by
    dsimp [xi]
    rw [abs_div, abs_neg, abs_of_pos hpi]
    field_simp [hpi.ne']
  have hbase : 1 + |d| ≤ R * (1 + |xi|) := by
    dsimp [R]
    rw [hd]
    nlinarith [abs_nonneg xi, Real.pi_pos]
  have hpow : (1 + |d|) ^ 10 ≤ R ^ (10 : ℕ) * (1 + |xi|) ^ 10 := by
    calc
      (1 + |d|) ^ 10 ≤ (R * (1 + |xi|)) ^ 10 := by gcongr
      _ = R ^ (10 : ℕ) * (1 + |xi|) ^ 10 := by rw [mul_pow]
  calc
    (1 + |d|) ^ 10 *
        ‖𝓕 (fun u : ℝ => complexifiedBumpFamily cutoff s u)
          (-d / (2 * Real.pi))‖
        ≤ (R ^ (10 : ℕ) * (1 + |xi|) ^ 10) *
          ‖𝓕 (fun u : ℝ => complexifiedBumpFamily cutoff s u) xi‖ := by
            simpa [xi] using mul_le_mul_of_nonneg_right hpow
              (norm_nonneg (𝓕 (fun u : ℝ => complexifiedBumpFamily cutoff s u) xi))
    _ = R ^ (10 : ℕ) *
        ((1 + |xi|) ^ 10 *
          ‖𝓕 (fun u : ℝ => complexifiedBumpFamily cutoff s u) xi‖) := by ring
    _ ≤ R ^ (10 : ℕ) * K := by
      gcongr
      exact hDecay s xi

/-- Pointwise form of the preceding estimate, expressed with the exact Schur
kernel used above. -/
theorem complexifiedLogScaleBumpFourier_norm_le_decay
    (cutoff : GMSmoothCutoff) {K s d : ℝ}
    (hDecay : (1 + |d|) ^ 10 *
      ‖complexifiedLogScaleBumpFourier cutoff
        ((d : ℂ) - I * (s : ℂ))‖ ≤ K) :
    ‖complexifiedLogScaleBumpFourier cutoff
        ((d : ℂ) - I * (s : ℂ))‖ ≤
      K * (1 / (1 + |d|) ^ (10 : ℕ)) := by
  have hbase : 0 < 1 + |d| := by positivity
  rw [mul_one_div]
  rw [le_div_iff₀ (pow_pos hbase 10)]
  simpa [mul_comm] using hDecay

/-- The exact complex Fourier kernel attached to a pair of zeta zeros. -/
noncomputable def zeroPairFourierKernel
    (cutoff : GMSmoothCutoff) (rho rho' : ℂ) : ℂ :=
  complexifiedLogScaleBumpFourier cutoff
    (((rho.im - rho'.im : ℝ) : ℂ) -
      I * ((rho.re + rho'.re : ℝ) : ℂ))

theorem zeroPairFourierKernel_eq_integral
    (cutoff : GMSmoothCutoff) (rho rho' : ℂ) :
    zeroPairFourierKernel cutoff rho rho' =
      ∫ u : ℝ, logScaleBumpComplex cutoff u *
        Complex.exp ((u : ℂ) * rho) *
        Complex.exp ((u : ℂ) * starRingEnd ℂ rho') := by
  unfold zeroPairFourierKernel complexifiedLogScaleBumpFourier
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  have hReorder :
      logScaleBumpComplex cutoff u * Complex.exp ((u : ℂ) * rho) *
          Complex.exp ((u : ℂ) * starRingEnd ℂ rho') =
        logScaleBumpComplex cutoff u *
          (Complex.exp ((u : ℂ) * rho) *
            Complex.exp ((u : ℂ) * starRingEnd ℂ rho')) := by ring
  rw [hReorder, ← Complex.exp_add]
  apply congrArg (fun q : ℂ => logScaleBumpComplex cutoff u * q)
  congr 1
  apply Complex.ext <;> simp
  · ring
  · ring

theorem integrable_zeroPairFourierKernel_integrand
    (cutoff : GMSmoothCutoff) (rho rho' : ℂ) :
    MeasureTheory.Integrable (fun u : ℝ =>
      logScaleBumpComplex cutoff u *
        Complex.exp ((u : ℂ) * rho) *
        Complex.exp ((u : ℂ) * starRingEnd ℂ rho')) := by
  have hcont : Continuous (fun u : ℝ =>
      logScaleBumpComplex cutoff u *
        Complex.exp ((u : ℂ) * rho) *
        Complex.exp ((u : ℂ) * starRingEnd ℂ rho')) := by
    have hb : Continuous (logScaleBumpComplex cutoff) :=
      (contDiff_logScaleBumpComplex cutoff).continuous
    have hr : Continuous (fun u : ℝ => Complex.exp ((u : ℂ) * rho)) := by
      fun_prop
    have hr' : Continuous (fun u : ℝ =>
        Complex.exp ((u : ℂ) * starRingEnd ℂ rho')) := by
      fun_prop
    exact (hb.mul hr).mul hr'
  have hsupp : HasCompactSupport (fun u : ℝ =>
      logScaleBumpComplex cutoff u *
        Complex.exp ((u : ℂ) * rho) *
        Complex.exp ((u : ℂ) * starRingEnd ℂ rho')) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro u hu
    by_contra hne
    apply hu
    apply support_logScaleBumpComplex cutoff
    rw [Function.mem_support]
    intro hzero
    apply hne
    rw [hzero]
    simp
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- The coefficient independent of logarithmic position in the strip sum. -/
noncomputable def stripZeroCoefficient (tau X : ℝ) (rho : ℂ) : ℂ :=
  (zeroMultiplicity rho : ℂ) * zeroIncrementCoefficient tau rho *
    (X : ℂ) ^ rho

/-- The exact strip sum after `x = X exp u`, before integration. -/
noncomputable def logarithmicZeroStripSum
    (sigmaLower sigmaUpper T tau X u : ℝ) : ℂ :=
  ∑ rho ∈ zerosInRect sigmaLower sigmaUpper (-T) T,
    stripZeroCoefficient tau X rho * Complex.exp ((u : ℂ) * rho)

/-- The compactly weighted complex second moment in logarithmic coordinates. -/
noncomputable def logarithmicZeroStripSecondMoment
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) : ℂ :=
  ∫ u : ℝ, logScaleBumpComplex cutoff u *
    logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u *
    starRingEnd ℂ (logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u)

/-- Real nonnegative version of the same logarithmic second moment. -/
noncomputable def logarithmicZeroStripNormMoment
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) : ℝ :=
  ∫ u : ℝ, logScaleBump cutoff u *
    ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 2

theorem integrable_logarithmicZeroStripNormMoment_integrand
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ => logScaleBump cutoff u *
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 2) := by
  have hsum : Continuous (fun u : ℝ =>
      logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) := by
    unfold logarithmicZeroStripSum
    fun_prop
  have hcont : Continuous (fun u : ℝ => logScaleBump cutoff u *
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 2) := by
    exact (contDiff_logScaleBump cutoff).continuous.mul
      (hsum.norm.pow 2)
  have hsupp : HasCompactSupport (fun u : ℝ => logScaleBump cutoff u *
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 2) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro u hu
    by_contra hne
    apply hu
    apply support_logScaleBump cutoff
    rw [Function.mem_support]
    intro hzero
    apply hne
    rw [hzero]
    simp
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem mul_starRingEnd_eq_norm_sq (z : ℂ) :
    z * starRingEnd ℂ z = (‖z‖ ^ 2 : ℂ) := by
  change z * star z = (‖z‖ ^ 2 : ℂ)
  exact RCLike.mul_conj z

/-- The complex pair-expansion moment is exactly the coercion of the
nonnegative real norm-square moment. -/
theorem logarithmicZeroStripSecondMoment_eq_ofReal_normMoment
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    logarithmicZeroStripSecondMoment cutoff sigmaLower sigmaUpper T tau X =
      (logarithmicZeroStripNormMoment cutoff
        sigmaLower sigmaUpper T tau X : ℂ) := by
  unfold logarithmicZeroStripSecondMoment logarithmicZeroStripNormMoment
  rw [← integral_complex_ofReal]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  rw [mul_assoc, mul_starRingEnd_eq_norm_sq]
  simp [logScaleBumpComplex]

theorem logarithmicZeroStripNormMoment_nonneg
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    0 ≤ logarithmicZeroStripNormMoment cutoff
      sigmaLower sigmaUpper T tau X := by
  unfold logarithmicZeroStripNormMoment
  apply MeasureTheory.integral_nonneg
  intro u
  exact mul_nonneg (logScaleBump_nonneg cutoff u) (sq_nonneg _)

theorem norm_logarithmicZeroStripSecondMoment_eq_normMoment
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    ‖logarithmicZeroStripSecondMoment cutoff
      sigmaLower sigmaUpper T tau X‖ =
      logarithmicZeroStripNormMoment cutoff
        sigmaLower sigmaUpper T tau X := by
  rw [logarithmicZeroStripSecondMoment_eq_ofReal_normMoment]
  simp [abs_of_nonneg (logarithmicZeroStripNormMoment_nonneg cutoff
    sigmaLower sigmaUpper T tau X)]

private theorem star_exp_real_mul (u : ℝ) (rho : ℂ) :
    starRingEnd ℂ (Complex.exp ((u : ℂ) * rho)) =
      Complex.exp ((u : ℂ) * starRingEnd ℂ rho) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem logarithmicZeroStripSecondMoment_integrand_eq_pair_sum
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X u : ℝ) :
    logScaleBumpComplex cutoff u *
        logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u *
        starRingEnd ℂ
          (logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) =
      ∑ rho ∈ zerosInRect sigmaLower sigmaUpper (-T) T,
        ∑ rho' ∈ zerosInRect sigmaLower sigmaUpper (-T) T,
          (stripZeroCoefficient tau X rho *
            starRingEnd ℂ (stripZeroCoefficient tau X rho')) *
          (logScaleBumpComplex cutoff u *
            Complex.exp ((u : ℂ) * rho) *
            Complex.exp ((u : ℂ) * starRingEnd ℂ rho')) := by
  classical
  unfold logarithmicZeroStripSum
  simp only [map_sum, map_mul]
  simp_rw [star_exp_real_mul]
  rw [mul_assoc]
  rw [Finset.sum_mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho' hrho'
  ring

/-- Exact finite pair expansion of the compactly weighted strip moment.  No
absolute-convergence issue is hidden here: both zero sets are finite, and the
remaining kernel integral is compactly supported. -/
theorem logarithmicZeroStripSecondMoment_eq_pair_sum
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    logarithmicZeroStripSecondMoment cutoff sigmaLower sigmaUpper T tau X =
      ∑ rho ∈ zerosInRect sigmaLower sigmaUpper (-T) T,
        ∑ rho' ∈ zerosInRect sigmaLower sigmaUpper (-T) T,
          (stripZeroCoefficient tau X rho *
            starRingEnd ℂ (stripZeroCoefficient tau X rho')) *
          zeroPairFourierKernel cutoff rho rho' := by
  classical
  unfold logarithmicZeroStripSecondMoment
  simp_rw [logarithmicZeroStripSecondMoment_integrand_eq_pair_sum]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro rho hrho
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro rho' hrho'
      rw [MeasureTheory.integral_const_mul]
      rw [← zeroPairFourierKernel_eq_integral]
    · intro rho' hrho'
      exact (integrable_zeroPairFourierKernel_integrand cutoff rho rho').const_mul _
  · intro rho hrho
    apply MeasureTheory.integrable_finsetSum _
    intro rho' hrho'
    exact (integrable_zeroPairFourierKernel_integrand cutoff rho rho').const_mul _

theorem zeroPairDecay_nonneg (rho rho' : ℂ) :
    0 ≤ zeroPairDecay rho rho' := by
  unfold zeroPairDecay
  positivity

/-- Uniform decay of the literal complex Fourier kernel at a pair of
critical-strip points. -/
theorem norm_zeroPairFourierKernel_le
    (cutoff : GMSmoothCutoff) {K : ℝ}
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {rho rho' : ℂ}
    (hrhoLower : 0 ≤ rho.re) (hrhoUpper : rho.re ≤ 1)
    (hrho'Lower : 0 ≤ rho'.re) (hrho'Upper : rho'.re ≤ 1) :
    ‖zeroPairFourierKernel cutoff rho rho'‖ ≤
      K * zeroPairDecay rho rho' := by
  have hs : rho.re + rho'.re ∈ Set.Icc (0 : ℝ) 2 := by
    constructor <;> linarith
  have h := complexifiedLogScaleBumpFourier_norm_le_decay cutoff
    (hDecay (rho.re + rho'.re) hs (rho.im - rho'.im))
  simpa [zeroPairFourierKernel, zeroPairDecay] using h

/-- The strip coefficient has exactly one analytic-multiplicity factor and
the source bound `X^sigmaUpper / tau`. -/
theorem norm_stripZeroCoefficient_le
    {tau X sigmaUpper : ℝ} (htau : 0 < tau) (hX : 1 ≤ X)
    {rho : ℂ} (hrhoNe : rho ≠ 0) (hrhoUpper : rho.re ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    ‖stripZeroCoefficient tau X rho‖ ≤
      (zeroMultiplicity rho : ℝ) * (X ^ sigmaUpper / tau) := by
  have hCoeff := norm_zeroIncrementCoefficient_le htau hrhoNe
    (hrhoUpper.trans hsigmaUpper)
  have hPow : X ^ rho.re ≤ X ^ sigmaUpper := by
    exact Real.rpow_le_rpow_of_exponent_le hX hrhoUpper
  unfold stripZeroCoefficient
  rw [norm_mul, norm_mul, RCLike.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hX)]
  calc
    (zeroMultiplicity rho : ℝ) * ‖zeroIncrementCoefficient tau rho‖ * X ^ rho.re
        ≤ (zeroMultiplicity rho : ℝ) * (1 / tau) * X ^ sigmaUpper := by
          gcongr
    _ = (zeroMultiplicity rho : ℝ) * (X ^ sigmaUpper / tau) := by ring

/-- Restricting both variables from the full symmetric zero set to a closed
real-part strip can only decrease the nonnegative decay sum. -/
theorem stripZeroPairDecaySum_le
    {sigmaLower sigmaUpper T : ℝ} (hsigmaUpper : sigmaUpper ≤ 1) :
    (∑ rho ∈ zerosInRect sigmaLower sigmaUpper (-T) T,
        (zeroMultiplicity rho : ℝ) *
          ∑ rho' ∈ zerosInRect sigmaLower sigmaUpper (-T) T,
            (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho') ≤
      zeroPairDecaySum sigmaLower T := by
  classical
  unfold zeroPairDecaySum
  let strip := zerosInRect sigmaLower sigmaUpper (-T) T
  let full := zeroSet sigmaLower T
  have hsubset : strip ⊆ full := zerosInRect_strip_subset_zeroSet hsigmaUpper
  change (∑ rho ∈ strip, (zeroMultiplicity rho : ℝ) *
      ∑ rho' ∈ strip,
        (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho') ≤
    ∑ rho ∈ full, (zeroMultiplicity rho : ℝ) *
      ∑ rho' ∈ full,
        (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho'
  calc
    (∑ rho ∈ strip, (zeroMultiplicity rho : ℝ) *
        ∑ rho' ∈ strip,
          (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho') ≤
      ∑ rho ∈ strip, (zeroMultiplicity rho : ℝ) *
        ∑ rho' ∈ full,
          (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho' := by
        apply Finset.sum_le_sum
        intro rho hrho
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro rho' _ _
          exact mul_nonneg (by positivity) (zeroPairDecay_nonneg rho rho')
        · positivity
    _ ≤ ∑ rho ∈ full, (zeroMultiplicity rho : ℝ) *
        ∑ rho' ∈ full,
          (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho' := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro rho _ _
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun rho' _ =>
        mul_nonneg (by positivity) (zeroPairDecay_nonneg rho rho'))

/-- The complete finite analytic estimate in Lemma 2.3 before substituting a
zero-density exponent and the physical formula for `T`.  It retains the
literal bump constant, local-zero-count constant, logarithm, and analytic
multiplicity. -/
theorem norm_logarithmicZeroStripSecondMoment_le
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {sigmaLower sigmaUpper T tau X : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hT : max (Real.exp 2) 8 ≤ T)
    (htau : 0 < tau) (hX : 1 ≤ X) :
    ‖logarithmicZeroStripSecondMoment cutoff
        sigmaLower sigmaUpper T tau X‖ ≤
      (K * ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau))) *
        (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log T * (zeroCount sigmaLower T : ℝ))) := by
  classical
  let strip := zerosInRect sigmaLower sigmaUpper (-T) T
  let R : ℝ := X ^ sigmaUpper / tau
  have hR : 0 ≤ R := by
    exact div_nonneg (Real.rpow_nonneg (by positivity) _) htau.le
  rw [logarithmicZeroStripSecondMoment_eq_pair_sum]
  calc
    ‖∑ rho ∈ strip, ∑ rho' ∈ strip,
        (stripZeroCoefficient tau X rho *
          starRingEnd ℂ (stripZeroCoefficient tau X rho')) *
        zeroPairFourierKernel cutoff rho rho'‖ ≤
      ∑ rho ∈ strip, ∑ rho' ∈ strip,
        ‖(stripZeroCoefficient tau X rho *
          starRingEnd ℂ (stripZeroCoefficient tau X rho')) *
        zeroPairFourierKernel cutoff rho rho'‖ := by
          exact norm_sum_le _ _ |>.trans (Finset.sum_le_sum fun rho _ =>
            norm_sum_le _ _)
    _ ≤ ∑ rho ∈ strip, ∑ rho' ∈ strip,
        (K * (R * R)) *
          ((zeroMultiplicity rho : ℝ) *
            ((zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho')) := by
      apply Finset.sum_le_sum
      intro rho hrho
      apply Finset.sum_le_sum
      intro rho' hrho'
      have hrhoMem : rho ∈ zerosInRect sigmaLower sigmaUpper (-T) T := by
        simpa [strip] using hrho
      have hrho'Mem : rho' ∈ zerosInRect sigmaLower sigmaUpper (-T) T := by
        simpa [strip] using hrho'
      have hrhoRect : rho ∈ RiemannZeta.GuthMaynard.ZeroRectangle
          sigmaLower sigmaUpper (-T) T := by
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrhoMem
        exact hrhoMem.1
      have hrho'Rect : rho' ∈ RiemannZeta.GuthMaynard.ZeroRectangle
          sigmaLower sigmaUpper (-T) T := by
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho'Mem
        exact hrho'Mem.1
      have hrhoBounds :=
        (RiemannZeta.GuthMaynard.mem_ZeroRectangle
          sigmaLower sigmaUpper (-T) T rho).mp hrhoRect
      have hrho'Bounds :=
        (RiemannZeta.GuthMaynard.mem_ZeroRectangle
          sigmaLower sigmaUpper (-T) T rho').mp hrho'Rect
      have hrhoReNonneg : 0 ≤ rho.re := hsigmaLower.trans hrhoBounds.1
      have hrho'ReNonneg : 0 ≤ rho'.re := hsigmaLower.trans hrho'Bounds.1
      have hrhoZero : riemannZeta rho = 0 := by
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrhoMem
        exact hrhoMem.2
      have hrho'Zero : riemannZeta rho' = 0 := by
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho'Mem
        exact hrho'Mem.2
      have hrhoRePos := zero_re_pos_of_nonneg hrhoReNonneg
        (hrhoBounds.2.1.trans hsigmaUpper) hrhoZero
      have hrho'RePos := zero_re_pos_of_nonneg hrho'ReNonneg
        (hrho'Bounds.2.1.trans hsigmaUpper) hrho'Zero
      have hrhoNe : rho ≠ 0 := by
        intro h
        subst rho
        norm_num at hrhoRePos
      have hrho'Ne : rho' ≠ 0 := by
        intro h
        subst rho'
        norm_num at hrho'RePos
      have hCoeff := norm_stripZeroCoefficient_le htau hX
        hrhoNe
        hrhoBounds.2.1 hsigmaUpper
      have hCoeff' := norm_stripZeroCoefficient_le htau hX
        hrho'Ne
        hrho'Bounds.2.1 hsigmaUpper
      have hKernel := norm_zeroPairFourierKernel_le cutoff hDecay
        hrhoReNonneg
        (hrhoBounds.2.1.trans hsigmaUpper)
        hrho'ReNonneg
        (hrho'Bounds.2.1.trans hsigmaUpper)
      have hStarNorm :
          ‖starRingEnd ℂ (stripZeroCoefficient tau X rho')‖ =
            ‖stripZeroCoefficient tau X rho'‖ := by
        change ‖star (stripZeroCoefficient tau X rho')‖ =
          ‖stripZeroCoefficient tau X rho'‖
        exact norm_star _
      rw [norm_mul, norm_mul, hStarNorm]
      change ‖stripZeroCoefficient tau X rho‖ *
          ‖stripZeroCoefficient tau X rho'‖ *
            ‖zeroPairFourierKernel cutoff rho rho'‖ ≤ _
      calc
        ‖stripZeroCoefficient tau X rho‖ *
            ‖stripZeroCoefficient tau X rho'‖ *
              ‖zeroPairFourierKernel cutoff rho rho'‖ ≤
          ((zeroMultiplicity rho : ℝ) * R) *
            ((zeroMultiplicity rho' : ℝ) * R) *
              (K * zeroPairDecay rho rho') := by gcongr
        _ = (K * (R * R)) *
            ((zeroMultiplicity rho : ℝ) *
              ((zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho')) := by ring
    _ = (K * (R * R)) *
        (∑ rho ∈ strip, (zeroMultiplicity rho : ℝ) *
          ∑ rho' ∈ strip,
            (zeroMultiplicity rho' : ℝ) * zeroPairDecay rho rho') := by
      simp only [Finset.mul_sum]
    _ ≤ (K * (R * R)) * zeroPairDecaySum sigmaLower T := by
      apply mul_le_mul_of_nonneg_left
      · simpa [strip] using stripZeroPairDecaySum_le hsigmaUpper
      · exact mul_nonneg hK (mul_nonneg hR hR)
    _ ≤ (K * (R * R)) *
        (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log T * (zeroCount sigmaLower T : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (zeroPairDecaySum_le sigmaLower T hsigmaLower hT)
        (mul_nonneg hK (mul_nonneg hR hR))
    _ = (K * ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau))) *
        (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log T * (zeroCount sigmaLower T : ℝ))) := by rfl

private theorem ofReal_exp_cpow (u : ℝ) (rho : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ rho = Complex.exp ((u : ℂ) * rho) := by
  rw [Complex.cpow_def_of_ne_zero]
  · have hlog : Complex.log ((Real.exp u : ℝ) : ℂ) = (u : ℂ) := by
      have h := Complex.log_ofReal_mul (Real.exp_pos u)
        (x := (1 : ℂ)) one_ne_zero
      simpa [Real.log_exp] using h
    rw [hlog]
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)

/-- Exact identification of the physical strip increment at `x = X exp u`
with the logarithmic finite sum used in the Fourier expansion. -/
theorem zeroStripIncrementSum_mul_exp_eq_logarithmicZeroStripSum
    {sigmaLower sigmaUpper T tau X u : ℝ}
    (htau : 0 < tau) (hX : 0 ≤ X) :
    zeroStripIncrementSum sigmaLower sigmaUpper T tau (X * Real.exp u) =
      logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u := by
  classical
  unfold zeroStripIncrementSum logarithmicZeroStripSum stripZeroCoefficient
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [zeroIncrementTerm_eq_cpow_mul_coefficient htau
    (mul_nonneg hX (Real.exp_pos u).le)]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hX
    (Real.exp_pos u).le, ofReal_exp_cpow]
  ring

/-- The paper's normalized physical `L²` moment on `[X,2X]`. -/
noncomputable def zeroStripPhysicalSecondMoment
    (sigmaLower sigmaUpper T tau X : ℝ) : ℝ :=
  (1 / X) * ∫ x : ℝ in X..2 * X,
    ‖zeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ^ 2

/-- Exact logarithmic change of variables, including the Jacobian. -/
theorem zeroStripPhysicalSecondMoment_eq_logarithmic
    {sigmaLower sigmaUpper T tau X : ℝ}
    (htau : 0 < tau) (hX : 0 < X) :
    zeroStripPhysicalSecondMoment sigmaLower sigmaUpper T tau X =
      ∫ u : ℝ in 0..Real.log 2,
        ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 2 *
          Real.exp u := by
  let g : ℝ → ℝ := fun x =>
    ‖zeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ^ 2
  let f : ℝ → ℝ := fun u => X * Real.exp u
  have hSub :
      (∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * f u) =
        ∫ x : ℝ in X..2 * X, g x := by
    have hChange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := Real.log 2) (f := f) (f' := f) (g := g)
      (by fun_prop)
      (by
        intro u hu
        exact (Real.hasDerivAt_exp u).const_mul X)
      (by
        intro u hu
        exact mul_nonneg hX.le (Real.exp_pos u).le)
    simpa [f, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm] using hChange
  unfold zeroStripPhysicalSecondMoment
  change (1 / X) * (∫ x : ℝ in X..2 * X, g x) = _
  rw [← hSub]
  have hFactor :
      (∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * f u) =
        X * ∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * Real.exp u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [f]
    ring
  rw [hFactor]
  field_simp [hX.ne']
  apply intervalIntegral.integral_congr
  intro u hu
  change ‖zeroStripIncrementSum sigmaLower sigmaUpper T tau
      (X * Real.exp u)‖ ^ 2 * Real.exp u = _
  rw [zeroStripIncrementSum_mul_exp_eq_logarithmicZeroStripSum htau hX.le]

/-- The physical interval moment is controlled by the compactly supported
logarithmic moment.  The explicit factor `2` is the Jacobian bound on
`0 ≤ u ≤ log 2`. -/
theorem zeroStripPhysicalSecondMoment_le_logarithmicNormMoment
    (cutoff : GMSmoothCutoff)
    {sigmaLower sigmaUpper T tau X : ℝ}
    (htau : 0 < tau) (hX : 0 < X) :
    zeroStripPhysicalSecondMoment sigmaLower sigmaUpper T tau X ≤
      2 * logarithmicZeroStripNormMoment cutoff
        sigmaLower sigmaUpper T tau X := by
  let q : ℝ → ℝ := fun u =>
    ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 2
  have hsum : Continuous (fun u : ℝ =>
      logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) := by
    unfold logarithmicZeroStripSum
    fun_prop
  have hq : Continuous q := by
    exact hsum.norm.pow 2
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hInterval :
      (∫ u : ℝ in 0..Real.log 2, q u * Real.exp u) ≤
        ∫ u : ℝ in 0..Real.log 2, 2 * q u := by
    apply intervalIntegral.integral_mono_on hlogTwo
      ((hq.mul Real.continuous_exp).intervalIntegrable 0 (Real.log 2))
      ((continuous_const.mul hq).intervalIntegrable 0 (Real.log 2))
    intro u hu
    change q u * Real.exp u ≤ 2 * q u
    have hExp : Real.exp u ≤ 2 := by
      calc
        Real.exp u ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hu.2
        _ = 2 := Real.exp_log (by norm_num)
    nlinarith [sq_nonneg
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖]
  have hRestricted :
      (∫ u : ℝ in 0..Real.log 2, q u) =
        ∫ u : ℝ in Set.Ioc 0 (Real.log 2),
          logScaleBump cutoff u * q u := by
    rw [intervalIntegral.integral_of_le hlogTwo]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (measurableSet_Ioc : MeasurableSet (Set.Ioc 0 (Real.log 2)))] with u hu
    rw [logScaleBump_eq_one cutoff (Set.Ioc_subset_Icc_self hu)]
    simp
  have hRestrictedLe :
      (∫ u : ℝ in 0..Real.log 2, q u) ≤
        logarithmicZeroStripNormMoment cutoff
          sigmaLower sigmaUpper T tau X := by
    rw [hRestricted]
    unfold logarithmicZeroStripNormMoment
    exact MeasureTheory.setIntegral_le_integral
      (integrable_logarithmicZeroStripNormMoment_integrand cutoff
        sigmaLower sigmaUpper T tau X)
      (Filter.Eventually.of_forall fun u =>
        mul_nonneg (logScaleBump_nonneg cutoff u) (sq_nonneg _))
  rw [zeroStripPhysicalSecondMoment_eq_logarithmic htau hX]
  change (∫ u : ℝ in 0..Real.log 2, q u * Real.exp u) ≤ _
  calc
    (∫ u : ℝ in 0..Real.log 2, q u * Real.exp u) ≤
        ∫ u : ℝ in 0..Real.log 2, 2 * q u := hInterval
    _ = 2 * ∫ u : ℝ in 0..Real.log 2, q u := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 2 * logarithmicZeroStripNormMoment cutoff
        sigmaLower sigmaUpper T tau X := by gcongr

/-- Full finite source estimate for the normalized physical `L²` moment. -/
theorem zeroStripPhysicalSecondMoment_le_count
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {sigmaLower sigmaUpper T tau X : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hT : max (Real.exp 2) 8 ≤ T)
    (htau : 0 < tau) (hX : 1 ≤ X) :
    zeroStripPhysicalSecondMoment sigmaLower sigmaUpper T tau X ≤
      2 * ((K * ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau))) *
        (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log T * (zeroCount sigmaLower T : ℝ)))) := by
  calc
    zeroStripPhysicalSecondMoment sigmaLower sigmaUpper T tau X ≤
        2 * logarithmicZeroStripNormMoment cutoff
          sigmaLower sigmaUpper T tau X :=
      zeroStripPhysicalSecondMoment_le_logarithmicNormMoment cutoff
        htau (zero_lt_one.trans_le hX)
    _ = 2 * ‖logarithmicZeroStripSecondMoment cutoff
        sigmaLower sigmaUpper T tau X‖ := by
      rw [norm_logarithmicZeroStripSecondMoment_eq_normMoment]
    _ ≤ 2 * ((K * ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau))) *
        (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log T * (zeroCount sigmaLower T : ℝ)))) := by
      gcongr
      exact norm_logarithmicZeroStripSecondMoment_le cutoff hK hDecay
        hsigmaLower hsigmaUpper hT htau hX

/-- A logarithm of the physical truncation height costs an arbitrarily small
power of `X`.  This is proved by composing the standard `log = o(x^eta)`
estimate with the actual height, then using its explicit power bound. -/
theorem eventually_abs_log_explicitFormulaHeight_le_rpow
    {J theta eps : ℝ} (hJ : 0 < J) (htheta : theta < 1)
    (heps : 0 < eps) :
    ∀ᶠ X : ℝ in Filter.atTop,
      |Real.log (explicitFormulaHeight J theta X)| ≤ X ^ eps := by
  let eta : ℝ := eps / (2 - theta)
  have hden : 0 < 2 - theta := by linarith
  have heta : 0 < eta := div_pos heps hden
  have hSmall := ((isLittleO_log_rpow_atTop heta).comp_tendsto
    (tendsto_explicitFormulaHeight_atTop hJ htheta)).eventuallyLE
  have hHeight := eventually_explicitFormulaHeight_le_rpow
    (J := J) (theta := theta) (q := (1 : ℝ)) zero_lt_one
  filter_upwards [hSmall, hHeight, eventually_ge_atTop (Real.exp 1)] with X
      hSmallX hHeightX hX
  have hExpOne : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1)
  have hXOne : 1 < X := hExpOne.trans_le hX
  have hXPos : 0 < X := zero_lt_one.trans hXOne
  have hHeightPos : 0 < explicitFormulaHeight J theta X :=
    explicitFormulaHeight_pos hJ hXOne
  have hPow := Real.rpow_le_rpow hHeightPos.le hHeightX heta.le
  calc
    |Real.log (explicitFormulaHeight J theta X)| =
        ‖Real.log (explicitFormulaHeight J theta X)‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ‖explicitFormulaHeight J theta X ^ eta‖ := hSmallX
    _ = explicitFormulaHeight J theta X ^ eta := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hHeightPos.le eta)]
    _ ≤ (X ^ (1 - theta + 1)) ^ eta := hPow
    _ = X ^ ((1 - theta + 1) * eta) :=
      (Real.rpow_mul hXPos.le _ _).symm
    _ = X ^ eps := by
      congr 1
      dsimp [eta]
      field_simp
      ring

/-- Multiplying the physical-height zero count by its single logarithm does
not change the central epsilon exponent. -/
theorem log_mul_zeroCount_at_explicitFormulaHeight_epsilonBound
    {J theta sigma a : ℝ} (hJ : 0 < J) (htheta : theta < 1)
    (ha : 0 ≤ a) (hsigma : sigma ≤ 1)
    (hDensity : ZeroDensityEnvelope sigma a) :
    EpsilonExponentBound
      (fun X => Real.log (explicitFormulaHeight J theta X) *
        (zeroCount sigma (explicitFormulaHeight J theta X) : ℝ))
      ((1 - theta) * (a * (1 - sigma))) := by
  have hCount := zeroDensityEnvelope_at_explicitFormulaHeight
    hJ htheta ha hsigma hDensity
  unfold EpsilonExponentBound at hCount ⊢
  intro eps heps
  have hepsHalf : 0 < eps / 2 := half_pos heps
  have hLogEventually := eventually_abs_log_explicitFormulaHeight_le_rpow
    hJ htheta hepsHalf
  have hLog :
      (fun X : ℝ => |Real.log (explicitFormulaHeight J theta X)|) =O[atTop]
        (fun X : ℝ => X ^ (eps / 2)) := by
    apply IsBigO.of_bound 1
    filter_upwards [hLogEventually, eventually_ge_atTop (1 : ℝ)] with X hLogX hX
    rw [Real.norm_eq_abs, abs_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul]
    exact hLogX
  have hProduct := hLog.mul (hCount (eps / 2) hepsHalf)
  have hLeft :
      (fun X : ℝ =>
        |Real.log (explicitFormulaHeight J theta X) *
          (zeroCount sigma (explicitFormulaHeight J theta X) : ℝ)|) =ᶠ[atTop]
      (fun X : ℝ =>
        |Real.log (explicitFormulaHeight J theta X)| *
          |(zeroCount sigma (explicitFormulaHeight J theta X) : ℝ)|) := by
    filter_upwards [] with X
    rw [abs_mul]
  have hRight :
      (fun X : ℝ => X ^ (eps / 2) *
        (X ^ (eps / 2) *
          |X ^ ((1 - theta) * (a * (1 - sigma)))|)) =ᶠ[atTop]
      (fun X : ℝ => X ^ eps *
        |X ^ ((1 - theta) * (a * (1 - sigma)))|) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hPow : X ^ (eps / 2) * X ^ (eps / 2) = X ^ eps := by
      rw [← Real.rpow_add hX]
      congr 1
      ring
    rw [← mul_assoc, hPow]
  exact hProduct.congr' hLeft.symm hRight

/-- The exact physical majorant after the finite Schur estimate. -/
noncomputable def zeroStripSecondPhysicalMajorant
    (J theta sigmaLower sigmaUpper X : ℝ) : ℝ :=
  (X ^ (theta + sigmaUpper - 1) * X ^ (theta + sigmaUpper - 1)) *
    (Real.log (explicitFormulaHeight J theta X) *
      (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ))

/-- Source exponent of the second-moment majorant. -/
theorem zeroStripSecondPhysicalMajorant_epsilonBound
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (htheta : theta < 1) (ha : 0 ≤ a)
    (hsigmaLower : sigmaLower ≤ 1)
    (hDensity : ZeroDensityEnvelope sigmaLower a) :
    EpsilonExponentBound
      (zeroStripSecondPhysicalMajorant J theta sigmaLower sigmaUpper)
      ((1 - theta) * (a * (1 - sigmaLower)) +
        2 * theta + 2 * sigmaUpper - 2) := by
  let d : ℝ := (1 - theta) * (a * (1 - sigmaLower))
  let s : ℝ := theta + sigmaUpper - 1
  have hLogCount := log_mul_zeroCount_at_explicitFormulaHeight_epsilonBound
    hJ htheta ha hsigmaLower hDensity
  unfold EpsilonExponentBound at hLogCount ⊢
  have hScaled :=
    RiemannZeta.GuthMaynard.EpsilonPowerBound.mul_left_rpow
      hLogCount (2 * s)
  intro eps heps
  have h := hScaled eps heps
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    unfold zeroStripSecondPhysicalMajorant
    have hPow : X ^ s * X ^ s = X ^ (2 * s) := by
      rw [← Real.rpow_add hX]
      congr 1
      ring
    simp [s, hPow]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hPow : X ^ (2 * s) * X ^ d =
        X ^ (d + 2 * theta + 2 * sigmaUpper - 2) := by
      rw [← Real.rpow_add hX]
      congr 1
      dsimp [s]
      ring
    rw [hPow]

theorem zeroStripPhysicalSecondMoment_nonneg
    {sigmaLower sigmaUpper T tau X : ℝ} (hX : 0 < X) :
    0 ≤ zeroStripPhysicalSecondMoment sigmaLower sigmaUpper T tau X := by
  unfold zeroStripPhysicalSecondMoment
  apply mul_nonneg (one_div_nonneg.mpr hX.le)
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x hx
  exact sq_nonneg _

/-- Pointwise physical majorization after inserting the exact source scale
`tau = X^(1-theta)` and height `T = J log(X)^2 tau`. -/
theorem zeroStripPhysicalSecondMoment_le_majorant
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {J theta sigmaLower sigmaUpper X : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hHeight : max (Real.exp 2) 8 ≤ explicitFormulaHeight J theta X)
    (hX : 1 ≤ X) :
    zeroStripPhysicalSecondMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X ≤
      (2 * K *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant)) *
        zeroStripSecondPhysicalMajorant J theta sigmaLower sigmaUpper X := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hFinite := zeroStripPhysicalSecondMoment_le_count cutoff hK hDecay
    (T := explicitFormulaHeight J theta X) (tau := localTau X theta)
    (X := X) hsigmaLower hsigmaUpper hHeight (localTau_pos hXPos) hX
  have hScale : X ^ sigmaUpper / localTau X theta =
      X ^ (theta + sigmaUpper - 1) := rpow_div_localTau hXPos
  unfold zeroStripSecondPhysicalMajorant
  calc
    zeroStripPhysicalSecondMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X ≤
      2 * ((K * (X ^ (theta + sigmaUpper - 1) *
        X ^ (theta + sigmaUpper - 1))) *
        (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log (explicitFormulaHeight J theta X) *
            (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ)))) :=
      by simpa only [hScale] using hFinite
    _ = (2 * K *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant)) *
        ((X ^ (theta + sigmaUpper - 1) * X ^ (theta + sigmaUpper - 1)) *
          (Real.log (explicitFormulaHeight J theta X) *
            (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ))) := by
      ring

/-- Full source-form Gafni--Tao Lemma 2.3.  The proof consumes the actual
finite zero strip, analytic multiplicities, local zero count, Fourier decay,
physical height, and ordinary zero-density envelope. -/
theorem zeroStripPhysicalSecondMoment_epsilonBound
    (cutoff : GMSmoothCutoff)
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (htheta : theta < 1) (ha : 0 ≤ a)
    (hsigmaLower : 0 ≤ sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hDensity : ZeroDensityEnvelope sigmaLower a) :
    EpsilonExponentBound
      (fun X => zeroStripPhysicalSecondMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X)
      ((1 - theta) * (a * (1 - sigmaLower)) +
        2 * theta + 2 * sigmaUpper - 2) := by
  obtain ⟨K, hK, hDecay⟩ :=
    exists_complexifiedLogScaleBumpFourier_tenfold_decay cutoff
  let C : ℝ := 2 * K *
    ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by positivity) hK)
      (mul_nonneg
        (mul_nonneg (by positivity) integerBinDecayMass_nonneg)
        globalLocalZeroLogConstant_pos.le)
  have hHeightEventually :
      ∀ᶠ X : ℝ in atTop,
        max (Real.exp 2) 8 ≤ explicitFormulaHeight J theta X :=
    (tendsto_explicitFormulaHeight_atTop hJ htheta).eventually
      (eventually_ge_atTop _)
  have hDomination :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (fun X => zeroStripPhysicalSecondMoment sigmaLower sigmaUpper
          (explicitFormulaHeight J theta X) (localTau X theta) X)
        (zeroStripSecondPhysicalMajorant J theta sigmaLower sigmaUpper) := by
    intro eps heps
    have hFixed :
        (fun X : ℝ =>
          |zeroStripPhysicalSecondMoment sigmaLower sigmaUpper
            (explicitFormulaHeight J theta X) (localTau X theta) X|) =O[atTop]
          (fun X : ℝ =>
            |zeroStripSecondPhysicalMajorant J theta sigmaLower sigmaUpper X|) := by
      apply IsBigO.of_bound C
      filter_upwards [hHeightEventually,
        eventually_ge_atTop (Real.exp 1)] with X hHeight hX
      have hExpOne : 1 < Real.exp 1 := by
        simpa only [Real.exp_zero] using
          Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1)
      have hXOne : 1 ≤ X := hExpOne.le.trans hX
      have hXPos : 0 < X := zero_lt_one.trans hExpOne |>.trans_le hX
      have hPoint := zeroStripPhysicalSecondMoment_le_majorant
        cutoff hK hDecay hsigmaLower hsigmaUpper hHeight hXOne
      have hHeightPos : 0 < explicitFormulaHeight J theta X :=
        explicitFormulaHeight_pos hJ (hExpOne.trans_le hX)
      have hMajorantNonneg :
          0 ≤ zeroStripSecondPhysicalMajorant J theta sigmaLower sigmaUpper X := by
        unfold zeroStripSecondPhysicalMajorant
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hXPos.le _)
            (Real.rpow_nonneg hXPos.le _))
          (mul_nonneg (Real.log_nonneg (by
            exact (Real.one_lt_exp_iff.mpr (by norm_num)).le.trans
              (le_trans (le_max_left _ _) hHeight))) (by positivity))
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg
        (zeroStripPhysicalSecondMoment_nonneg hXPos), Real.norm_eq_abs, abs_abs,
        abs_of_nonneg hMajorantNonneg]
      simpa [C] using hPoint
    exact hFixed.trans
      ((RiemannZeta.GuthMaynard.EpsilonPowerBound.refl
        (zeroStripSecondPhysicalMajorant J theta sigmaLower sigmaUpper)) eps heps)
  exact hDomination.trans
    (zeroStripSecondPhysicalMajorant_epsilonBound hJ htheta ha
      (hsigmaOrder.trans hsigmaUpper) hDensity)

end GafniTao

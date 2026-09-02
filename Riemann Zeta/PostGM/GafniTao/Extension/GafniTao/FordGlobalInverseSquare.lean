import GafniTao.FordInverseSquareBinMass

/-!
# The complete nonlocal inverse-square zero bound

This file sums the zeros outside Ford's local disk.  It works with the actual
finite symmetric zero set and analytic multiplicity, and the resulting bound
is uniform in the finite height cutoff.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def fordNonlocalInverseSquare
    (t T q : ℝ) : ℝ :=
  ∑ rho ∈ (zeroSet 0 T).filter (fun rho =>
      q ≤ fordLocalDistance t rho),
    (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2

private theorem ford_halfInteger_abs_pos (n : ℤ) :
    0 < |(n : ℝ) + 1 / 2| := by
  rw [abs_pos]
  intro hn
  have htwo : (2 : ℝ) * n + 1 = 0 := by linarith
  have hcast : ((2 * n + 1 : ℤ) : ℝ) = 0 := by
    norm_num at htwo ⊢
    exact htwo
  have hint : 2 * n + 1 = 0 := by exact_mod_cast hcast
  omega

theorem ford_ordinate_decay_le_bin_decay
    (t : ℝ) (rho : ℂ) :
    1 / (1 + |t - rho.im|) ^ (2 : ℕ) ≤
      9 * fordInverseSquareBinDecay
        (ordinateBin rho - ⌊t⌋) := by
  let a : ℝ := (⌊t⌋ : ℤ)
  let b : ℝ := (⌊rho.im⌋ : ℤ)
  have haLower : a ≤ t := Int.floor_le t
  have haUpper : t < a + 1 := Int.lt_floor_add_one t
  have hbLower : b ≤ rho.im := Int.floor_le rho.im
  have hbUpper : rho.im < b + 1 := Int.lt_floor_add_one rho.im
  have hba : |b - rho.im| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hta : |t - a| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hshift : |b - a + 1 / 2| ≤ 3 * (1 + |t - rho.im|) := by
    have heq : b - a + 1 / 2 =
        (b - rho.im) + (rho.im - t) + (t - a) + 1 / 2 := by ring
    rw [heq]
    calc
      |(b - rho.im) + (rho.im - t) + (t - a) + 1 / 2| ≤
          |(b - rho.im) + (rho.im - t) + (t - a)| + |(1 / 2 : ℝ)| :=
        abs_add_le _ _
      _ ≤ (|(b - rho.im) + (rho.im - t)| + |t - a|) +
          |(1 / 2 : ℝ)| := by
        linarith [abs_add_le ((b - rho.im) + (rho.im - t)) (t - a)]
      _ ≤ ((|b - rho.im| + |rho.im - t|) + |t - a|) +
          |(1 / 2 : ℝ)| := by
        linarith [abs_add_le (b - rho.im) (rho.im - t)]
      _ ≤ 1 + |t - rho.im| + 1 + 1 / 2 := by
        rw [abs_sub_comm rho.im t, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        gcongr
      _ ≤ 3 * (1 + |t - rho.im|) := by
        linarith [abs_nonneg (t - rho.im)]
  have hbase : 0 < 1 + |t - rho.im| := by positivity
  have hhalf : 0 <
      |(((ordinateBin rho - ⌊t⌋ : ℤ) : ℝ)) + 1 / 2| :=
    ford_halfInteger_abs_pos _
  have hcast : (((ordinateBin rho - ⌊t⌋ : ℤ) : ℝ)) = b - a := by
    simp [ordinateBin, a, b]
  have hpow :
      |(((ordinateBin rho - ⌊t⌋ : ℤ) : ℝ)) + 1 / 2| ^ (2 : ℕ) ≤
        (3 * (1 + |t - rho.im|)) ^ (2 : ℕ) := by
    rw [hcast]
    gcongr
  unfold fordInverseSquareBinDecay
  rw [mul_one_div]
  rw [div_le_div_iff₀ (pow_pos hbase 2) (pow_pos hhalf 2)]
  calc
    1 * |(((ordinateBin rho - ⌊t⌋ : ℤ) : ℝ)) + 1 / 2| ^ (2 : ℕ) ≤
        (3 * (1 + |t - rho.im|)) ^ (2 : ℕ) := by simpa using hpow
    _ = 9 * (1 + |t - rho.im|) ^ (2 : ℕ) := by ring

theorem ford_inv_distance_sq_le_ordinate_decay
    {t q : ℝ} {rho : ℂ}
    (hq : 1 / 4 ≤ q) (hrho : q ≤ fordLocalDistance t rho) :
    1 / fordLocalDistance t rho ^ 2 ≤
      25 / (1 + |t - rho.im|) ^ 2 := by
  have hdistQuarter : (1 / 4 : ℝ) ≤ fordLocalDistance t rho := hq.trans hrho
  have hdistPos : 0 < fordLocalDistance t rho := by linarith
  have him : |t - rho.im| ≤ fordLocalDistance t rho := by
    unfold fordLocalDistance
    simpa [mul_comm] using
      Complex.abs_im_le_norm ((1 : ℂ) + I * (t : ℂ) - rho)
  have hlinear : 1 + |t - rho.im| ≤ 5 * fordLocalDistance t rho := by
    nlinarith
  have hsq : (1 + |t - rho.im|) ^ 2 ≤
      25 * fordLocalDistance t rho ^ 2 := by
    have hmul := mul_self_le_mul_self
      (by positivity : 0 ≤ 1 + |t - rho.im|) hlinear
    nlinarith
  have hbasePos : 0 < 1 + |t - rho.im| := by positivity
  rw [div_le_div_iff₀ (sq_pos_of_pos hdistPos) (sq_pos_of_pos hbasePos)]
  nlinarith

theorem ford_inv_distance_sq_le_bin_decay
    {t q : ℝ} {rho : ℂ}
    (hq : 1 / 4 ≤ q) (hrho : q ≤ fordLocalDistance t rho) :
    1 / fordLocalDistance t rho ^ 2 ≤
      225 * fordInverseSquareBinDecay
        (ordinateBin rho - ⌊t⌋) := by
  calc
    1 / fordLocalDistance t rho ^ 2 ≤
        25 / (1 + |t - rho.im|) ^ 2 :=
      ford_inv_distance_sq_le_ordinate_decay hq hrho
    _ = 25 * (1 / (1 + |t - rho.im|) ^ 2) := by ring
    _ ≤ 25 * (9 * fordInverseSquareBinDecay
        (ordinateBin rho - ⌊t⌋)) := by
      gcongr
      exact ford_ordinate_decay_le_bin_decay t rho
    _ = 225 * fordInverseSquareBinDecay
        (ordinateBin rho - ⌊t⌋) := by ring

/-- The global nonlocal zero tail is uniform in `T` and has only one
logarithm of the physical height. -/
theorem fordNonlocalInverseSquare_le
    {t T q : ℝ} (hq : 1 / 4 ≤ q) :
    fordNonlocalInverseSquare t T q ≤
      225 * globalLocalZeroLogConstant *
        (Real.log (fordAdaptiveZeroBinHeight ⌊t⌋) *
            fordInverseSquareBinMass +
          fordInverseSquareBinLogMass) := by
  let S := (zeroSet 0 T).filter (fun rho => q ≤ fordLocalDistance t rho)
  let bins : Finset ℤ := S.image ordinateBin
  let a : ℤ := ⌊t⌋
  have hAll : S.filter (fun w => ordinateBin w ∈ bins) = S := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S bins ordinateBin
    (fun rho => (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2)
  rw [hAll] at hFiber
  have hLogNonneg (z : ℤ) :
      0 ≤ Real.log (fordAdaptiveZeroBinHeight z) :=
    Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 8).trans
      (fordAdaptiveZeroBinHeight_ge_eight z))
  have hEach : ∀ z ∈ bins,
      ∑ rho ∈ S.filter (fun w => ordinateBin w = z),
          (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2 ≤
        225 * fordInverseSquareBinDecay (z - a) *
          (globalLocalZeroLogConstant *
            Real.log (fordAdaptiveZeroBinHeight z)) := by
    intro z hz
    have hSubset : S.filter (fun w => ordinateBin w = z) ⊆
        (zeroSet 0 T).filter (fun w => ordinateBin w = z) := by
      intro rho hrho
      rw [Finset.mem_filter] at hrho ⊢
      exact ⟨(Finset.mem_filter.mp hrho.1).1, hrho.2⟩
    have hMultNat :
        ∑ rho ∈ S.filter (fun w => ordinateBin w = z), zeroMultiplicity rho ≤
          ∑ rho ∈ (zeroSet 0 T).filter (fun w => ordinateBin w = z),
            zeroMultiplicity rho := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun _ _ _ => Nat.zero_le _)
    have hMult :
        ((∑ rho ∈ S.filter (fun w => ordinateBin w = z),
          zeroMultiplicity rho : ℕ) : ℝ) ≤
        globalLocalZeroLogConstant *
          Real.log (fordAdaptiveZeroBinHeight z) := by
      have hcast :
          ((∑ rho ∈ S.filter (fun w => ordinateBin w = z),
            zeroMultiplicity rho : ℕ) : ℝ) ≤
          ((∑ rho ∈ (zeroSet 0 T).filter (fun w => ordinateBin w = z),
            zeroMultiplicity rho : ℕ) : ℝ) := by exact_mod_cast hMultNat
      exact hcast.trans (floorFiber_multiplicity_le_adaptive_log T z)
    calc
      ∑ rho ∈ S.filter (fun w => ordinateBin w = z),
          (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2 ≤
        ∑ rho ∈ S.filter (fun w => ordinateBin w = z),
          (zeroMultiplicity rho : ℝ) *
            (225 * fordInverseSquareBinDecay (z - a)) := by
        apply Finset.sum_le_sum
        intro rho hrho
        rw [Finset.mem_filter] at hrho
        have hnonlocal := (Finset.mem_filter.mp hrho.1).2
        have hpoint := ford_inv_distance_sq_le_bin_decay hq hnonlocal
        calc
          (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2 =
              (zeroMultiplicity rho : ℝ) *
                (1 / fordLocalDistance t rho ^ 2) := by ring
          _ ≤ (zeroMultiplicity rho : ℝ) *
              (225 * fordInverseSquareBinDecay (z - a)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            simpa [a, hrho.2] using hpoint
      _ = 225 * fordInverseSquareBinDecay (z - a) *
          ((∑ rho ∈ S.filter (fun w => ordinateBin w = z),
            zeroMultiplicity rho : ℕ) : ℝ) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro rho hrho
        ring
      _ ≤ 225 * fordInverseSquareBinDecay (z - a) *
          (globalLocalZeroLogConstant *
            Real.log (fordAdaptiveZeroBinHeight z)) := by
        exact mul_le_mul_of_nonneg_left hMult
          (mul_nonneg (by norm_num) (fordInverseSquareBinDecay_nonneg _))
  unfold fordNonlocalInverseSquare
  change ∑ rho ∈ S, (zeroMultiplicity rho : ℝ) /
      fordLocalDistance t rho ^ 2 ≤ _
  calc
    ∑ rho ∈ S, (zeroMultiplicity rho : ℝ) /
        fordLocalDistance t rho ^ 2 =
      ∑ z ∈ bins, ∑ rho ∈ S.filter (fun w => ordinateBin w = z),
        (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2 := hFiber.symm
    _ ≤ ∑ z ∈ bins, 225 * fordInverseSquareBinDecay (z - a) *
        (globalLocalZeroLogConstant *
          Real.log (fordAdaptiveZeroBinHeight z)) := Finset.sum_le_sum hEach
    _ = 225 * globalLocalZeroLogConstant *
        (∑ z ∈ bins, fordInverseSquareBinDecay (z - a) *
          Real.log (fordAdaptiveZeroBinHeight z)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ ≤ 225 * globalLocalZeroLogConstant *
        (Real.log (fordAdaptiveZeroBinHeight a) *
            fordInverseSquareBinMass + fordInverseSquareBinLogMass) := by
      exact mul_le_mul_of_nonneg_left
        (sum_fordInverseSquareBinDecay_mul_adaptiveLog_le bins a)
        (mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le)
    _ = _ := by rfl

#print axioms fordNonlocalInverseSquare_le

end

end GafniTao

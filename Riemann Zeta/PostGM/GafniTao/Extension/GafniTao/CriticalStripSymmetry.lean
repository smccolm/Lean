import GafniTao.CriticalStripReflection
import RiemannZeta.GuthMaynard.ClassicalDensity

/-!
# Critical-strip reflection and the lower-half zero count

The published Gafni--Tao convention uses the elementary exponent
`A(σ) = 1 / (1 - σ)` on `0 ≤ σ ≤ 1/2`.  The frozen Jensen estimate is stated
only from the critical line to the right.  This file supplies the missing
source bridge: reflect the left half of the critical strip through `s ↦ 1-s`,
preserve analytic multiplicity, and compare the complete strip with twice the
right half.  No Riemann--von Mangoldt postulate is introduced.
-/

open scoped BigOperators

namespace GafniTao

open Complex Filter
open RiemannZeta.GuthMaynard

/-- The full source count from any `0 ≤ σ ≤ 1/2` is bounded by twice the
critical-line count.  The factor two is the exact cost of splitting at the
critical line and reflecting the left half; analytic multiplicity is
preserved term by term. -/
theorem zeroCount_le_two_mul_half
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) :
    zeroCount sigma T ≤ 2 * zeroCount (1 / 2) T := by
  classical
  let S := zeroSet sigma T
  let U := S.filter fun z => (1 / 2 : ℝ) ≤ z.re
  let L := S.filter fun z => ¬(1 / 2 : ℝ) ≤ z.re
  let H := zeroSet (1 / 2) T
  have hUpperSubset : U ⊆ H := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzS, hzHalf⟩
    change z ∈ zerosInRect sigma 1 (-T) T at hzS
    change z ∈ zerosInRect (1 / 2) 1 (-T) T
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff]
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hzS
    rcases hzS with ⟨hzRect, hzZero⟩
    rw [mem_ZeroRectangle] at hzRect ⊢
    exact ⟨⟨hzHalf, hzRect.2.1, hzRect.2.2.1, hzRect.2.2.2⟩, hzZero⟩
  have hLowerReflectMem : ∀ z ∈ L, criticalStripReflect z ∈ H := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzS, hzLower⟩
    change z ∈ zerosInRect sigma 1 (-T) T at hzS
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hzS
    rcases hzS with ⟨hzRect, hzZero⟩
    rw [mem_ZeroRectangle] at hzRect
    have hzNonneg : 0 ≤ z.re := hsigma.trans hzRect.1
    have hzRePos := zero_re_pos_of_nonneg hzNonneg hzRect.2.1 hzZero
    have hzReUpper := zero_re_lt_one_of_le_one hzRect.2.1 hzZero
    change criticalStripReflect z ∈ zerosInRect (1 / 2) 1 (-T) T
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle]
    refine ⟨⟨?_, ?_, ?_, ?_⟩,
      riemannZeta_criticalStripReflect_eq_zero hzRePos hzReUpper hzZero⟩
    · simp [criticalStripReflect]
      linarith
    · simp [criticalStripReflect]
      linarith
    · simp [criticalStripReflect]
      linarith [hzRect.2.2.2]
    · simp [criticalStripReflect]
      linarith [hzRect.2.2.1]
  have hUpperLe :
      ∑ z ∈ U, zeroMultiplicity z ≤ ∑ z ∈ H, zeroMultiplicity z := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hUpperSubset
      (fun _ _ _ => Nat.zero_le _)
  have hReflectInjective : Function.Injective criticalStripReflect := by
    intro z w h
    unfold criticalStripReflect at h
    linear_combination -h
  have hLowerImageSubset : L.image criticalStripReflect ⊆ H := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hLowerReflectMem w hw
  have hLowerMultiplicity : ∀ z ∈ L,
      zeroMultiplicity (criticalStripReflect z) = zeroMultiplicity z := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzS, _⟩
    change z ∈ zerosInRect sigma 1 (-T) T at hzS
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hzS
    rcases hzS with ⟨hzRect, hzZero⟩
    rw [mem_ZeroRectangle] at hzRect
    have hzNonneg : 0 ≤ z.re := hsigma.trans hzRect.1
    exact zeroMultiplicity_criticalStripReflect
      (zero_re_pos_of_nonneg hzNonneg hzRect.2.1 hzZero)
      (zero_re_lt_one_of_le_one hzRect.2.1 hzZero)
  have hLowerSumEq :
      ∑ z ∈ L, zeroMultiplicity z =
        ∑ z ∈ L.image criticalStripReflect, zeroMultiplicity z := by
    rw [Finset.sum_image hReflectInjective.injOn]
    exact Finset.sum_congr rfl fun z hz => (hLowerMultiplicity z hz).symm
  have hLowerLe :
      ∑ z ∈ L, zeroMultiplicity z ≤ ∑ z ∈ H, zeroMultiplicity z := by
    rw [hLowerSumEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hLowerImageSubset
      (fun _ _ _ => Nat.zero_le _)
  have hPartition :
      ∑ z ∈ S, zeroMultiplicity z =
        (∑ z ∈ U, zeroMultiplicity z) + ∑ z ∈ L, zeroMultiplicity z := by
    simpa [U, L] using (Finset.sum_filter_add_sum_filter_not S
      (fun z => (1 / 2 : ℝ) ≤ z.re) zeroMultiplicity).symm
  rw [zeroCount_eq_weighted_sum, zeroCount_eq_weighted_sum]
  change (∑ z ∈ S, zeroMultiplicity z) ≤ 2 * ∑ z ∈ H, zeroMultiplicity z
  rw [hPartition]
  omega

/-- The complete source count has the elementary exponent one throughout the
closed lower half of the critical strip. -/
theorem lowerHalf_zeroCount_epsilon_one
    {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    EpsilonExponentBound (fun T => (zeroCount sigma T : ℝ)) 1 := by
  unfold EpsilonExponentBound
  intro eps heps
  have hHalf := global_zero_count_epsilon_one (1 / 2) (by norm_num)
  have hdom :
      (fun T : ℝ => |(zeroCount sigma T : ℝ)|) =O[atTop]
        (fun T : ℝ => |(zeroCount (1 / 2) T : ℝ)|) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [] with T
    rw [Real.norm_eq_abs, abs_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast zeroCount_le_two_mul_half (T := T) hsigma
  exact hdom.trans (hHalf eps heps)

/-- Source lower-half density envelope `A(σ) ≤ 1/(1-σ)`, obtained from the
kernel-checked Jensen count and critical-strip reflection. -/
theorem lowerHalf_zeroDensityEnvelope
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (hsigmaHalf : sigma ≤ 1 / 2) :
    ZeroDensityEnvelope sigma (1 / (1 - sigma)) := by
  unfold ZeroDensityEnvelope
  have hne : 1 - sigma ≠ 0 := by linarith
  convert lowerHalf_zeroCount_epsilon_one hsigma using 1
  field_simp

/-- The corresponding upper bound for the actual extended-real density
exponent. -/
theorem zeroDensityExponent_le_lowerHalf
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (hsigmaHalf : sigma ≤ 1 / 2) :
    zeroDensityExponent sigma ≤ ((1 / (1 - sigma) : ℝ) : EReal) :=
  zeroDensityExponent_le (lowerHalf_zeroDensityEnvelope hsigma hsigmaHalf)

end GafniTao

import GafniTao.SecondMoment

/-!
# The Gafni--Tao fourth-moment zero kernel

This file develops the pair-sum counting function and the exact finite
bridge from its same-bin energy to the source tolerance-one count `N*`.
-/

open Asymptotics Complex Finset Filter Set
open scoped BigOperators ContDiff FourierTransform

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- Ordered pairs of distinct zero representatives. -/
noncomputable def zeroPairs (sigma T : ℝ) : Finset (ℂ × ℂ) :=
  zeroSet sigma T ×ˢ zeroSet sigma T

/-- Product analytic multiplicity of a pair. -/
noncomputable def zeroPairWeight (p : ℂ × ℂ) : ℕ :=
  zeroMultiplicity p.1 * zeroMultiplicity p.2

/-- Sum of the two ordinates in a pair. -/
def zeroPairOrdinate (p : ℂ × ℂ) : ℝ := p.1.im + p.2.im

/-- Half-open unit bin containing the pair ordinate. -/
noncomputable def zeroPairBin (p : ℂ × ℂ) : ℤ := ⌊zeroPairOrdinate p⌋

/-- The actual multiplicity-weighted pair-count function `F`. -/
noncomputable def zeroPairBinCount (sigma T : ℝ) (z : ℤ) : ℕ :=
  ∑ p ∈ (zeroPairs sigma T).filter (fun q => zeroPairBin q = z),
    zeroPairWeight p

theorem zeroPairBinCount_nonneg (sigma T : ℝ) (z : ℤ) :
    0 ≤ zeroPairBinCount sigma T z := Nat.zero_le _

/-- Only finitely many integer bins have nonzero pair count. -/
theorem zeroPairBinCount_support_subset
    (sigma T : ℝ) :
    Function.support (zeroPairBinCount sigma T) ⊆
      (zeroPairs sigma T).image zeroPairBin := by
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hnot
  have hempty :
      (zeroPairs sigma T).filter (fun q => zeroPairBin q = z) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp heq
    apply hnot
    exact Finset.mem_image.mpr ⟨p, hp, heq⟩
  apply hz
  simp [zeroPairBinCount, hempty]

theorem summable_zeroPairBinCount (sigma T : ℝ) :
    Summable (fun z : ℤ => (zeroPairBinCount sigma T z : ℝ)) := by
  apply summable_of_ne_finset_zero
    (s := (zeroPairs sigma T).image zeroPairBin)
  intro z hz
  have hnot : z ∉ Function.support (zeroPairBinCount sigma T) := by
    intro hmem
    exact hz (zeroPairBinCount_support_subset sigma T hmem)
  simpa [Function.mem_support] using hnot

/-- Equal pair bins force tolerance strictly less than one. -/
theorem abs_zeroPairOrdinate_sub_lt_one_of_bin_eq
    {p q : ℂ × ℂ} (hbin : zeroPairBin p = zeroPairBin q) :
    |zeroPairOrdinate p - zeroPairOrdinate q| < 1 := by
  have hpLower : ((⌊zeroPairOrdinate p⌋ : ℤ) : ℝ) ≤ zeroPairOrdinate p :=
    Int.floor_le _
  have hpUpper : zeroPairOrdinate p < ((⌊zeroPairOrdinate p⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hqLower : ((⌊zeroPairOrdinate q⌋ : ℤ) : ℝ) ≤ zeroPairOrdinate q :=
    Int.floor_le _
  have hqUpper : zeroPairOrdinate q < ((⌊zeroPairOrdinate q⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  unfold zeroPairBin at hbin
  rw [abs_lt]
  change -1 < zeroPairOrdinate p - zeroPairOrdinate q ∧
    zeroPairOrdinate p - zeroPairOrdinate q < 1
  rw [hbin] at hpLower hpUpper
  constructor <;> linarith

/-- A quadruple assembled from two equal-bin pairs belongs to the exact
tolerance-one source energy set. -/
theorem pair_mem_resonantZeroQuadruples_of_bin_eq
    {sigma T : ℝ} {p q : ℂ × ℂ}
    (hp : p ∈ zeroPairs sigma T) (hq : q ∈ zeroPairs sigma T)
    (hbin : zeroPairBin p = zeroPairBin q) :
    (p, q) ∈ resonantZeroQuadruples sigma T := by
  rw [zeroPairs, Finset.mem_product] at hp hq
  rw [mem_resonantZeroQuadruples]
  refine ⟨hp.1, hp.2, hq.1, hq.2, ?_⟩
  have hlt := abs_zeroPairOrdinate_sub_lt_one_of_bin_eq hbin
  unfold zeroPairOrdinate at hlt
  have hrearrange :
      p.1.im + p.2.im - q.1.im - q.2.im =
        (p.1.im + p.2.im) - (q.1.im + q.2.im) := by ring
  rw [hrearrange]
  exact hlt.le

/-- The finite set of quadruples whose two pair sums lie in the same
half-open unit bin. -/
noncomputable def sameBinZeroQuadruples (sigma T : ℝ) :
    Finset ((ℂ × ℂ) × (ℂ × ℂ)) :=
  (zeroQuadruples sigma T).filter
    (fun q => zeroPairBin q.1 = zeroPairBin q.2)

theorem sameBinZeroQuadruples_subset_resonant
    (sigma T : ℝ) :
    sameBinZeroQuadruples sigma T ⊆ resonantZeroQuadruples sigma T := by
  intro q hq
  rw [sameBinZeroQuadruples, Finset.mem_filter] at hq
  rw [mem_zeroQuadruples] at hq
  apply pair_mem_resonantZeroQuadruples_of_bin_eq
  · rw [zeroPairs, Finset.mem_product]
    exact ⟨hq.1.1, hq.1.2.1⟩
  · rw [zeroPairs, Finset.mem_product]
    exact ⟨hq.1.2.2.1, hq.1.2.2.2⟩
  · exact hq.2

/-- Multiplicity-weighted same-bin pair energy. -/
noncomputable def sameBinZeroEnergy (sigma T : ℝ) : ℕ :=
  ∑ q ∈ sameBinZeroQuadruples sigma T, zeroQuadrupleWeight q

theorem sameBinZeroEnergy_le_zeroAdditiveEnergyCount
    (sigma T : ℝ) :
    sameBinZeroEnergy sigma T ≤ zeroAdditiveEnergyCount sigma T := by
  unfold sameBinZeroEnergy zeroAdditiveEnergyCount
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact sameBinZeroQuadruples_subset_resonant sigma T
  · intro q _ _
    exact Nat.zero_le _

/-- Finite support of the pair-count function. -/
noncomputable def zeroPairBins (sigma T : ℝ) : Finset ℤ :=
  (zeroPairs sigma T).image zeroPairBin

/-- The squared `L²` mass of the actual pair-count function. -/
noncomputable def zeroPairBinSquareSum (sigma T : ℝ) : ℕ :=
  ∑ z ∈ zeroPairBins sigma T, (zeroPairBinCount sigma T z) ^ 2

private theorem sum_sq_fibers
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (key : α → β) (weight : α → ℕ) :
    ∑ z ∈ S.image key,
        (∑ x ∈ S.filter (fun y => key y = z), weight x) ^ 2 =
      ∑ p ∈ S, ∑ q ∈ S,
        if key p = key q then weight p * weight q else 0 := by
  classical
  simp only [pow_two, Finset.sum_mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hkey : key p = key q
  · rw [Finset.sum_eq_single (key p)]
    · simp [hkey]
    · intro z hz hzne
      have hpne : key p ≠ z := fun hpz => hzne hpz.symm
      simp [hpne]
    · intro hnot
      exact (hnot (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).elim
  · simp [hkey]

/-- Double counting identifies the squared pair-bin mass with the weighted
same-bin quadruple count. -/
theorem zeroPairBinSquareSum_eq_sameBinZeroEnergy
    (sigma T : ℝ) :
    zeroPairBinSquareSum sigma T = sameBinZeroEnergy sigma T := by
  classical
  rw [zeroPairBinSquareSum, sameBinZeroEnergy]
  unfold zeroPairBins zeroPairBinCount
  rw [sum_sq_fibers (zeroPairs sigma T) zeroPairBin zeroPairWeight]
  unfold sameBinZeroQuadruples zeroQuadruples zeroPairs
  simp only [Finset.sum_filter, Finset.sum_product]
  simp [zeroPairWeight, zeroQuadrupleWeight]
  simp only [mul_assoc]

theorem zeroPairBinCount_eq_zero_of_not_mem_bins
    {sigma T : ℝ} {z : ℤ} (hz : z ∉ zeroPairBins sigma T) :
    zeroPairBinCount sigma T z = 0 := by
  by_contra hne
  have hsupp : z ∈ Function.support (zeroPairBinCount sigma T) := by
    simpa [Function.mem_support]
  exact hz (zeroPairBinCount_support_subset sigma T hsupp)

theorem summable_zeroPairBinCount_sq (sigma T : ℝ) :
    Summable (fun z : ℤ => (zeroPairBinCount sigma T z : ℝ) ^ 2) := by
  apply summable_of_ne_finset_zero (s := zeroPairBins sigma T)
  intro z hz
  rw [zeroPairBinCount_eq_zero_of_not_mem_bins hz]
  norm_num

/-- The real `ℓ²` mass of the actual pair-count function is the cast of the
finite same-bin energy. -/
theorem tsum_zeroPairBinCount_sq_eq_sameBinZeroEnergy
    (sigma T : ℝ) :
    ∑' z : ℤ, (zeroPairBinCount sigma T z : ℝ) ^ 2 =
      (sameBinZeroEnergy sigma T : ℝ) := by
  rw [tsum_eq_sum (s := zeroPairBins sigma T)]
  · rw [← zeroPairBinSquareSum_eq_sameBinZeroEnergy]
    simp [zeroPairBinSquareSum, Nat.cast_sum, Nat.cast_pow]
  · intro z hz
    rw [zeroPairBinCount_eq_zero_of_not_mem_bins hz]
    norm_num

/-- Every integer translate of the pair-count autocorrelation is controlled
by its same-bin energy.  This is the exact discrete Schur/Cauchy--Schwarz
step used before summing the Fourier kernel. -/
theorem zeroPairBinAutocorrelation_le_sameBinZeroEnergy
    (sigma T : ℝ) (k : ℤ) :
    (∑ z ∈ zeroPairBins sigma T,
        (zeroPairBinCount sigma T z : ℝ) *
          zeroPairBinCount sigma T (z - k)) ≤
      (sameBinZeroEnergy sigma T : ℝ) := by
  let F : ℤ → ℝ := fun z => zeroPairBinCount sigma T z
  let S : Finset ℤ := zeroPairBins sigma T
  have hSq : Summable (fun z : ℤ => F z ^ 2) := by
    simpa [F] using summable_zeroPairBinCount_sq sigma T
  have hShiftSq : Summable (fun z : ℤ => F (z - k) ^ 2) := by
    have hcomp := hSq.comp_injective (Equiv.subRight k).injective
    simpa [Function.comp_def] using hcomp
  have hShiftTsum :
      ∑' z : ℤ, F (z - k) ^ 2 = ∑' z : ℤ, F z ^ 2 := by
    simpa using (Equiv.subRight k).tsum_eq (fun z : ℤ => F z ^ 2)
  have hShiftFinite :
      (∑ z ∈ S, F (z - k) ^ 2) ≤ ∑' z : ℤ, F z ^ 2 := by
    calc
      (∑ z ∈ S, F (z - k) ^ 2) ≤ ∑' z : ℤ, F (z - k) ^ 2 :=
        hShiftSq.sum_le_tsum S (fun _ _ => sq_nonneg _)
      _ = ∑' z : ℤ, F z ^ 2 := hShiftTsum
  have hUnshifted :
      ∑ z ∈ S, F z ^ 2 = ∑' z : ℤ, F z ^ 2 := by
    symm
    apply tsum_eq_sum
    intro z hz
    rw [show F z = 0 by
      simpa [F] using zeroPairBinCount_eq_zero_of_not_mem_bins
        (sigma := sigma) (T := T) hz]
    norm_num
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S F (fun z => F (z - k))
  have hEnergy :
      ∑' z : ℤ, F z ^ 2 = (sameBinZeroEnergy sigma T : ℝ) := by
    simpa [F] using tsum_zeroPairBinCount_sq_eq_sameBinZeroEnergy sigma T
  have hSumNonneg : 0 ≤ ∑ z ∈ S, F z * F (z - k) := by
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hEnergyNonneg : 0 ≤ (sameBinZeroEnergy sigma T : ℝ) := Nat.cast_nonneg _
  have hSquare :
      (∑ z ∈ S, F z * F (z - k)) ^ 2 ≤
        (sameBinZeroEnergy sigma T : ℝ) ^ 2 := by
    calc
      (∑ z ∈ S, F z * F (z - k)) ^ 2 ≤
          (∑ z ∈ S, F z ^ 2) * (∑ z ∈ S, F (z - k) ^ 2) := hCS
      _ ≤ (sameBinZeroEnergy sigma T : ℝ) *
          (sameBinZeroEnergy sigma T : ℝ) := by
        rw [hUnshifted, hEnergy]
        exact mul_le_mul_of_nonneg_left
          (hShiftFinite.trans_eq hEnergy) hEnergyNonneg
      _ = (sameBinZeroEnergy sigma T : ℝ) ^ 2 := by ring
  change (∑ z ∈ S, F z * F (z - k)) ≤ _
  nlinarith

/-- The literal tenfold decay kernel between two sums of zero ordinates. -/
noncomputable def zeroPairPairDecay (p q : ℂ × ℂ) : ℝ :=
  1 / (1 + |zeroPairOrdinate p - zeroPairOrdinate q|) ^ (10 : ℕ)

theorem zeroPairPairDecay_nonneg (p q : ℂ × ℂ) :
    0 ≤ zeroPairPairDecay p q := by
  unfold zeroPairPairDecay
  positivity

/-- Passing the pair ordinates to half-open integer bins has the same explicit
`3^10` loss as the one-zero Schur kernel. -/
theorem zeroPairPairDecay_le_integerBinDecay (p q : ℂ × ℂ) :
    zeroPairPairDecay p q ≤
      3 ^ (10 : ℕ) * integerBinDecay (zeroPairBin q - zeroPairBin p) := by
  let rp : ℂ := I * (zeroPairOrdinate p : ℂ)
  let rq : ℂ := I * (zeroPairOrdinate q : ℂ)
  have h := zeroPairDecay_le_integerBinDecay rp rq
  simpa [zeroPairPairDecay, zeroPairDecay, zeroPairBin, rp, rq,
    abs_sub_comm] using h

/-- The exact multiplicity-weighted quadruple decay sum obtained after the
fourth-moment Fourier expansion. -/
noncomputable def zeroPairPairDecaySum (sigma T : ℝ) : ℝ :=
  ∑ p ∈ zeroPairs sigma T, ∑ q ∈ zeroPairs sigma T,
    (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
      zeroPairPairDecay p q

/-- The same sum after exact aggregation by the two pair-ordinate bins. -/
noncomputable def zeroPairBinKernelSum (sigma T : ℝ) : ℝ :=
  ∑ z ∈ zeroPairBins sigma T, ∑ w ∈ zeroPairBins sigma T,
    (zeroPairBinCount sigma T z : ℝ) *
      (zeroPairBinCount sigma T w : ℝ) * integerBinDecay (w - z)

noncomputable def zeroPairBinDifferences (sigma T : ℝ) : Finset ℤ :=
  ((zeroPairBins sigma T) ×ˢ (zeroPairBins sigma T)).image
    (fun zw => zw.2 - zw.1)

noncomputable def zeroPairBinDifferenceCorrelation
    (sigma T : ℝ) (k : ℤ) : ℝ :=
  ∑ zw ∈ ((zeroPairBins sigma T) ×ˢ (zeroPairBins sigma T)).filter
      (fun zw => zw.2 - zw.1 = k),
    (zeroPairBinCount sigma T zw.1 : ℝ) *
      zeroPairBinCount sigma T zw.2

theorem zeroPairBinDifferenceCorrelation_le_sameBinZeroEnergy
    (sigma T : ℝ) (k : ℤ) :
    zeroPairBinDifferenceCorrelation sigma T k ≤
      (sameBinZeroEnergy sigma T : ℝ) := by
  classical
  let S : Finset ℤ := zeroPairBins sigma T
  let F : ℤ → ℝ := fun z => zeroPairBinCount sigma T z
  have hInner (z : ℤ) (hz : z ∈ S) :
      (∑ w ∈ S, if w - z = k then F z * F w else 0) ≤
        F z * F (z + k) := by
    by_cases hmem : z + k ∈ S
    · rw [Finset.sum_eq_single (z + k)]
      · simp
      · intro w hw hne
        have hdiff : w - z ≠ k := by
          intro heq
          apply hne
          omega
        simp [hdiff]
      · intro hnot
        exact (hnot hmem).elim
    · have hzero : F (z + k) = 0 := by
        simpa [F, S] using zeroPairBinCount_eq_zero_of_not_mem_bins
          (sigma := sigma) (T := T) hmem
      rw [hzero, mul_zero]
      apply Finset.sum_nonpos
      intro w hw
      by_cases hdiff : w - z = k
      · have heq : w = z + k := by omega
        exact (hmem (heq ▸ hw)).elim
      · simp [hdiff]
  calc
    zeroPairBinDifferenceCorrelation sigma T k =
        ∑ z ∈ S, ∑ w ∈ S, if w - z = k then F z * F w else 0 := by
      unfold zeroPairBinDifferenceCorrelation
      rw [Finset.sum_filter, Finset.sum_product]
    _ ≤ ∑ z ∈ S, F z * F (z + k) := by
      apply Finset.sum_le_sum
      intro z hz
      exact hInner z hz
    _ ≤ (sameBinZeroEnergy sigma T : ℝ) := by
      simpa [F, S] using
        zeroPairBinAutocorrelation_le_sameBinZeroEnergy sigma T (-k)

theorem zeroPairBinDifferenceCorrelation_nonneg
    (sigma T : ℝ) (k : ℤ) :
    0 ≤ zeroPairBinDifferenceCorrelation sigma T k := by
  unfold zeroPairBinDifferenceCorrelation
  apply Finset.sum_nonneg
  intro zw hzw
  exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Exact finite regrouping of the bin kernel by the ordinate-bin
difference. -/
theorem zeroPairBinKernelSum_eq_differenceSum (sigma T : ℝ) :
    zeroPairBinKernelSum sigma T =
      ∑ k ∈ zeroPairBinDifferences sigma T,
        integerBinDecay k * zeroPairBinDifferenceCorrelation sigma T k := by
  classical
  let S : Finset ℤ := zeroPairBins sigma T
  let P : Finset (ℤ × ℤ) := S ×ˢ S
  let key : ℤ × ℤ → ℤ := fun zw => zw.2 - zw.1
  let W : ℤ → ℝ := fun z => zeroPairBinCount sigma T z
  have hmaps : ∀ zw ∈ P, key zw ∈ P.image key := by
    intro zw hzw
    exact Finset.mem_image.mpr ⟨zw, hzw, rfl⟩
  calc
    zeroPairBinKernelSum sigma T =
        ∑ zw ∈ P, W zw.1 * W zw.2 * integerBinDecay (key zw) := by
      unfold zeroPairBinKernelSum
      rw [Finset.sum_product]
    _ = ∑ k ∈ P.image key,
        ∑ zw ∈ P with key zw = k,
          W zw.1 * W zw.2 * integerBinDecay (key zw) := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps
        (fun zw => W zw.1 * W zw.2 * integerBinDecay (key zw))).symm
    _ = ∑ k ∈ P.image key,
        integerBinDecay k *
          (∑ zw ∈ P.filter (fun zw => key zw = k), W zw.1 * W zw.2) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro zw hzw
      rw [Finset.mem_filter] at hzw
      rw [hzw.2]
      ring
    _ = ∑ k ∈ zeroPairBinDifferences sigma T,
        integerBinDecay k * zeroPairBinDifferenceCorrelation sigma T k := by
      rfl

theorem zeroPairBinKernelSum_le_sameBinEnergy
    (sigma T : ℝ) :
    zeroPairBinKernelSum sigma T ≤
      integerBinDecayMass * (sameBinZeroEnergy sigma T : ℝ) := by
  rw [zeroPairBinKernelSum_eq_differenceSum]
  calc
    (∑ k ∈ zeroPairBinDifferences sigma T,
        integerBinDecay k * zeroPairBinDifferenceCorrelation sigma T k) ≤
        ∑ k ∈ zeroPairBinDifferences sigma T,
          integerBinDecay k * (sameBinZeroEnergy sigma T : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (zeroPairBinDifferenceCorrelation_le_sameBinZeroEnergy sigma T k)
        (integerBinDecay_nonneg k)
    _ = (∑ k ∈ zeroPairBinDifferences sigma T, integerBinDecay k) *
        (sameBinZeroEnergy sigma T : ℝ) := by rw [Finset.sum_mul]
    _ ≤ integerBinDecayMass * (sameBinZeroEnergy sigma T : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact (summable_integerBinDecay.sum_le_tsum
          (zeroPairBinDifferences sigma T)
          (fun k _ => integerBinDecay_nonneg k)).trans_eq rfl
      · exact Nat.cast_nonneg _

private theorem sum_kernel_over_fibers
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (key : α → β) (weight : α → ℝ)
    (kernel : β → β → ℝ) :
    (∑ a ∈ S.image key, ∑ b ∈ S.image key,
        (∑ x ∈ S.filter (fun y => key y = a), weight x) *
          (∑ y ∈ S.filter (fun x => key x = b), weight y) * kernel a b) =
      ∑ x ∈ S, ∑ y ∈ S, weight x * weight y * kernel (key x) (key y) := by
  classical
  let B : Finset β := S.image key
  have hmaps : ∀ x ∈ S, key x ∈ B := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hInner (a : β) (x : α) :
      (∑ b ∈ B, ∑ y ∈ S.filter (fun q => key q = b),
          weight x * weight y * kernel a b) =
        ∑ y ∈ S, weight x * weight y * kernel a (key y) := by
    calc
      (∑ b ∈ B, ∑ y ∈ S.filter (fun q => key q = b),
          weight x * weight y * kernel a b) =
          ∑ b ∈ B, ∑ y ∈ S with key y = b,
            weight x * weight y * kernel a (key y) := by
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [hy.2]
      _ = ∑ y ∈ S, weight x * weight y * kernel a (key y) :=
        Finset.sum_fiberwise_of_maps_to hmaps
          (fun y => weight x * weight y * kernel a (key y))
  calc
    (∑ a ∈ S.image key, ∑ b ∈ S.image key,
        (∑ x ∈ S.filter (fun y => key y = a), weight x) *
          (∑ y ∈ S.filter (fun x => key x = b), weight y) * kernel a b) =
        ∑ a ∈ B, ∑ x ∈ S.filter (fun q => key q = a),
          ∑ b ∈ B, ∑ y ∈ S.filter (fun q => key q = b),
            weight x * weight y * kernel a b := by
      apply Finset.sum_congr rfl
      intro a ha
      change
        (∑ b ∈ B,
          ((∑ x ∈ S.filter (fun q => key q = a), weight x) *
            (∑ y ∈ S.filter (fun q => key q = b), weight y)) * kernel a b) = _
      calc
        (∑ b ∈ B,
          ((∑ x ∈ S.filter (fun q => key q = a), weight x) *
            (∑ y ∈ S.filter (fun q => key q = b), weight y)) * kernel a b) =
            ∑ b ∈ B, ∑ x ∈ S.filter (fun q => key q = a),
              ∑ y ∈ S.filter (fun q => key q = b),
                weight x * weight y * kernel a b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_mul]
        _ = ∑ x ∈ S.filter (fun q => key q = a),
            ∑ b ∈ B, ∑ y ∈ S.filter (fun q => key q = b),
              weight x * weight y * kernel a b := by
          rw [Finset.sum_comm]
    _ = ∑ a ∈ B, ∑ x ∈ S.filter (fun q => key q = a),
        ∑ y ∈ S, weight x * weight y * kernel a (key y) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro x hx
      exact hInner a x
    _ = ∑ a ∈ B, ∑ x ∈ S with key x = a,
        ∑ y ∈ S, weight x * weight y * kernel (key x) (key y) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hx.2]
    _ = ∑ x ∈ S, ∑ y ∈ S,
        weight x * weight y * kernel (key x) (key y) :=
      Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => ∑ y ∈ S, weight x * weight y * kernel (key x) (key y))

noncomputable def zeroPairBinnedDecaySum (sigma T : ℝ) : ℝ :=
  ∑ p ∈ zeroPairs sigma T, ∑ q ∈ zeroPairs sigma T,
    (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
      integerBinDecay (zeroPairBin q - zeroPairBin p)

theorem zeroPairBinnedDecaySum_eq_binKernelSum (sigma T : ℝ) :
    zeroPairBinnedDecaySum sigma T = zeroPairBinKernelSum sigma T := by
  rw [zeroPairBinnedDecaySum, zeroPairBinKernelSum]
  symm
  simpa [zeroPairBins, zeroPairBinCount] using
    sum_kernel_over_fibers (zeroPairs sigma T) zeroPairBin
      (fun p => (zeroPairWeight p : ℝ))
      (fun z w => integerBinDecay (w - z))

/-- The complete four-zero decay sum is controlled by the exact source
tolerance-one additive energy.  This is the finite pair-count/double-counting
bridge in Gafni--Tao Lemma 2.4. -/
theorem zeroPairPairDecaySum_le_zeroAdditiveEnergyCount
    (sigma T : ℝ) :
    zeroPairPairDecaySum sigma T ≤
      (3 ^ (10 : ℕ) * integerBinDecayMass) *
        (zeroAdditiveEnergyCount sigma T : ℝ) := by
  have hPointwise : zeroPairPairDecaySum sigma T ≤
      3 ^ (10 : ℕ) * zeroPairBinnedDecaySum sigma T := by
    calc
      zeroPairPairDecaySum sigma T ≤
          ∑ p ∈ zeroPairs sigma T, ∑ q ∈ zeroPairs sigma T,
            (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
              (3 ^ (10 : ℕ) *
                integerBinDecay (zeroPairBin q - zeroPairBin p)) := by
        unfold zeroPairPairDecaySum
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · exact zeroPairPairDecay_le_integerBinDecay p q
        · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = 3 ^ (10 : ℕ) * zeroPairBinnedDecaySum sigma T := by
        unfold zeroPairBinnedDecaySum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
  calc
    zeroPairPairDecaySum sigma T ≤
        3 ^ (10 : ℕ) * zeroPairBinnedDecaySum sigma T := hPointwise
    _ = 3 ^ (10 : ℕ) * zeroPairBinKernelSum sigma T := by
      rw [zeroPairBinnedDecaySum_eq_binKernelSum]
    _ ≤ 3 ^ (10 : ℕ) *
        (integerBinDecayMass * (sameBinZeroEnergy sigma T : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (zeroPairBinKernelSum_le_sameBinEnergy sigma T) (by positivity)
    _ ≤ (3 ^ (10 : ℕ) * integerBinDecayMass) *
        (zeroAdditiveEnergyCount sigma T : ℝ) := by
      have hEnergy : (sameBinZeroEnergy sigma T : ℝ) ≤
          (zeroAdditiveEnergyCount sigma T : ℝ) := by
        exact_mod_cast sameBinZeroEnergy_le_zeroAdditiveEnergyCount sigma T
      have hConst : 0 ≤ 3 ^ (10 : ℕ) * integerBinDecayMass :=
        mul_nonneg (by positivity) integerBinDecayMass_nonneg
      calc
        3 ^ (10 : ℕ) *
            (integerBinDecayMass * (sameBinZeroEnergy sigma T : ℝ)) =
            (3 ^ (10 : ℕ) * integerBinDecayMass) *
              (sameBinZeroEnergy sigma T : ℝ) := by ring
        _ ≤ (3 ^ (10 : ℕ) * integerBinDecayMass) *
            (zeroAdditiveEnergyCount sigma T : ℝ) :=
          mul_le_mul_of_nonneg_left hEnergy hConst

/-- Compact parameter cutoff equal to one for every sum of four critical-strip
real parts. -/
noncomputable def quarticSpectralParameterBump
    (cutoff : GMSmoothCutoff) (s : ℝ) : ℝ :=
  cutoff (6 / 5 + 3 * s / 20)

theorem quarticSpectralParameterBump_eq_one
    (cutoff : GMSmoothCutoff) {s : ℝ} (hs : s ∈ Set.Icc 0 4) :
    quarticSpectralParameterBump cutoff s = 1 := by
  apply cutoff.equals_one
  rw [Set.mem_Icc] at hs ⊢
  constructor <;> linarith

theorem contDiff_quarticSpectralParameterBump (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (quarticSpectralParameterBump cutoff) := by
  exact cutoff.smooth.comp
    (contDiff_const.add ((contDiff_const.mul contDiff_id).div_const 20))

theorem support_quarticSpectralParameterBump (cutoff : GMSmoothCutoff) :
    Function.support (quarticSpectralParameterBump cutoff) ⊆
      Set.Icc (-4 / 3) (16 / 3) := by
  intro s hs
  have hrange := cutoff.support (by
    simpa only [quarticSpectralParameterBump, Function.mem_support] using hs)
  rw [Set.mem_Icc] at hrange ⊢
  constructor <;> linarith

noncomputable def quarticComplexifiedBumpFamily
    (cutoff : GMSmoothCutoff) (s u : ℝ) : ℂ :=
  (quarticSpectralParameterBump cutoff s : ℂ) *
    logScaleBumpComplex cutoff u * Complex.exp (((s * u : ℝ) : ℂ))

theorem contDiff_uncurry_quarticComplexifiedBumpFamily
    (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (Function.uncurry (quarticComplexifiedBumpFamily cutoff)) := by
  have hsReal : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => quarticSpectralParameterBump cutoff p.1) :=
    (contDiff_quarticSpectralParameterBump cutoff).comp contDiff_fst
  have hs : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => (quarticSpectralParameterBump cutoff p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsReal
  have hu : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => logScaleBumpComplex cutoff p.2) :=
    (contDiff_logScaleBumpComplex cutoff).comp contDiff_snd
  have hsuReal : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  have hsu : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => ((p.1 * p.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsuReal
  have hexp : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => Complex.exp (((p.1 * p.2 : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp hsu
  exact (hs.mul hu).mul hexp

theorem support_uncurry_quarticComplexifiedBumpFamily
    (cutoff : GMSmoothCutoff) :
    Function.support (Function.uncurry (quarticComplexifiedBumpFamily cutoff)) ⊆
      Set.Icc (-4 / 3) (16 / 3) ×ˢ Set.Icc (-2 / 5) (8 / 5) := by
  intro p hp
  rw [Function.mem_support] at hp
  constructor
  · apply support_quarticSpectralParameterBump cutoff
    rw [Function.mem_support]
    intro hzero
    apply hp
    change quarticComplexifiedBumpFamily cutoff p.1 p.2 = 0
    unfold quarticComplexifiedBumpFamily
    rw [hzero]
    simp
  · apply support_logScaleBumpComplex cutoff
    rw [Function.mem_support]
    intro hzero
    apply hp
    change quarticComplexifiedBumpFamily cutoff p.1 p.2 = 0
    unfold quarticComplexifiedBumpFamily
    rw [hzero]
    simp

theorem exists_quarticComplexifiedBumpFamily_tenfold_decay
    (cutoff : GMSmoothCutoff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s xi : ℝ,
      (1 + |xi|) ^ 10 *
        ‖𝓕 (fun u : ℝ => quarticComplexifiedBumpFamily cutoff s u) xi‖ ≤ K := by
  let F := quarticComplexifiedBumpFamily cutoff
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    contDiff_uncurry_quarticComplexifiedBumpFamily cutoff
  have hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc (-4 / 3) (16 / 3) ×ˢ Set.Icc (-2 / 5) (8 / 5) :=
    support_uncurry_quarticComplexifiedBumpFamily cutoff
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
      (1 + |xi|) ^ 10 * ‖𝓕 (fun u : ℝ => F s u) xi‖ ≤
          2 ^ (10 : ℕ) * K0 :=
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
      (1 + |xi|) ^ 10 * ‖𝓕 (fun u : ℝ => F s u) xi‖ ≤
          (2 ^ (10 : ℕ) * |xi| ^ 10) *
            ‖𝓕 (fun u : ℝ => F s u) xi‖ :=
        mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
      _ = 2 ^ (10 : ℕ) *
          (|xi| ^ 10 * ‖𝓕 (fun u : ℝ => F s u) xi‖) := by ring
      _ ≤ 2 ^ (10 : ℕ) * K10 := by gcongr
      _ ≤ 2 ^ (10 : ℕ) * (K0 + K10) := by
        gcongr
        exact le_add_of_nonneg_left hK0

theorem complexifiedLogScaleBumpFourier_eq_quarticFamily_fourier
    (cutoff : GMSmoothCutoff) {s : ℝ} (hs : s ∈ Set.Icc 0 4) (d : ℝ) :
    complexifiedLogScaleBumpFourier cutoff ((d : ℂ) - I * (s : ℂ)) =
      𝓕 (fun u : ℝ => quarticComplexifiedBumpFamily cutoff s u)
        (-d / (2 * Real.pi)) := by
  unfold complexifiedLogScaleBumpFourier
  rw [Real.fourier_eq']
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  unfold quarticComplexifiedBumpFamily
  rw [quarticSpectralParameterBump_eq_one cutoff hs]
  simp only [Complex.ofReal_one, one_mul, smul_eq_mul]
  have hReorder : Complex.exp
        (((-2 * Real.pi * inner ℝ u (-d / (2 * Real.pi)) : ℝ) : ℂ) * I) *
          (logScaleBumpComplex cutoff u * Complex.exp (((s * u : ℝ) : ℂ))) =
      logScaleBumpComplex cutoff u *
        (Complex.exp
          (((-2 * Real.pi * inner ℝ u (-d / (2 * Real.pi)) : ℝ) : ℂ) * I) *
          Complex.exp (((s * u : ℝ) : ℂ))) := by ring
  rw [hReorder, ← Complex.exp_add]
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

theorem exists_quarticComplexifiedLogScaleBumpFourier_tenfold_decay
    (cutoff : GMSmoothCutoff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc (0 : ℝ) 4, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K := by
  obtain ⟨K, hK, hDecay⟩ :=
    exists_quarticComplexifiedBumpFamily_tenfold_decay cutoff
  let R : ℝ := 1 + 2 * Real.pi
  refine ⟨R ^ (10 : ℕ) * K, mul_nonneg (by positivity) hK, ?_⟩
  intro s hs d
  rw [complexifiedLogScaleBumpFourier_eq_quarticFamily_fourier cutoff hs d]
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
  have hpow : (1 + |d|) ^ 10 ≤
      R ^ (10 : ℕ) * (1 + |xi|) ^ 10 := by
    calc
      (1 + |d|) ^ 10 ≤ (R * (1 + |xi|)) ^ 10 := by gcongr
      _ = R ^ (10 : ℕ) * (1 + |xi|) ^ 10 := by rw [mul_pow]
  calc
    (1 + |d|) ^ 10 *
        ‖𝓕 (fun u : ℝ => quarticComplexifiedBumpFamily cutoff s u)
          (-d / (2 * Real.pi))‖ ≤
        (R ^ (10 : ℕ) * (1 + |xi|) ^ 10) *
          ‖𝓕 (fun u : ℝ => quarticComplexifiedBumpFamily cutoff s u) xi‖ := by
      simpa [xi] using mul_le_mul_of_nonneg_right hpow
        (norm_nonneg
          (𝓕 (fun u : ℝ => quarticComplexifiedBumpFamily cutoff s u) xi))
    _ = R ^ (10 : ℕ) *
        ((1 + |xi|) ^ 10 *
          ‖𝓕 (fun u : ℝ => quarticComplexifiedBumpFamily cutoff s u) xi‖) := by
      ring
    _ ≤ R ^ (10 : ℕ) * K := by
      gcongr
      exact hDecay s xi

noncomputable def stripZeroPairCoefficient
    (tau X : ℝ) (p : ℂ × ℂ) : ℂ :=
  stripZeroCoefficient tau X p.1 * stripZeroCoefficient tau X p.2

noncomputable def logarithmicZeroStripPairSum
    (sigmaLower sigmaUpper T tau X u : ℝ) : ℂ :=
  ∑ p ∈ (zerosInRect sigmaLower sigmaUpper (-T) T ×ˢ
      zerosInRect sigmaLower sigmaUpper (-T) T),
    stripZeroPairCoefficient tau X p *
      Complex.exp ((u : ℂ) * (p.1 + p.2))

theorem logarithmicZeroStripPairSum_eq_sq
    (sigmaLower sigmaUpper T tau X u : ℝ) :
    logarithmicZeroStripPairSum sigmaLower sigmaUpper T tau X u =
      logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u *
        logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u := by
  classical
  unfold logarithmicZeroStripPairSum logarithmicZeroStripSum
  rw [Finset.sum_product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  apply Finset.sum_congr rfl
  intro rho' hrho'
  unfold stripZeroPairCoefficient
  have hexp :
      Complex.exp ((u : ℂ) * (rho + rho')) =
        Complex.exp ((u : ℂ) * rho) *
          Complex.exp ((u : ℂ) * rho') := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Exact fourth-moment Fourier kernel between two ordered zero pairs. -/
noncomputable def zeroPairPairFourierKernel
    (cutoff : GMSmoothCutoff) (p q : ℂ × ℂ) : ℂ :=
  complexifiedLogScaleBumpFourier cutoff
    (((zeroPairOrdinate p - zeroPairOrdinate q : ℝ) : ℂ) -
      I * (((p.1.re + p.2.re + q.1.re + q.2.re : ℝ) : ℂ)))

theorem zeroPairPairFourierKernel_eq_integral
    (cutoff : GMSmoothCutoff) (p q : ℂ × ℂ) :
    zeroPairPairFourierKernel cutoff p q =
      ∫ u : ℝ, logScaleBumpComplex cutoff u *
        Complex.exp ((u : ℂ) * (p.1 + p.2)) *
        Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2)) := by
  unfold zeroPairPairFourierKernel complexifiedLogScaleBumpFourier
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  have hReorder :
      logScaleBumpComplex cutoff u *
          Complex.exp ((u : ℂ) * (p.1 + p.2)) *
          Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2)) =
        logScaleBumpComplex cutoff u *
          (Complex.exp ((u : ℂ) * (p.1 + p.2)) *
            Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2))) := by ring
  rw [hReorder, ← Complex.exp_add]
  apply congrArg (fun z : ℂ => logScaleBumpComplex cutoff u * z)
  congr 1
  apply Complex.ext <;> simp [zeroPairOrdinate]
  · ring
  · ring

theorem integrable_zeroPairPairFourierKernel_integrand
    (cutoff : GMSmoothCutoff) (p q : ℂ × ℂ) :
    MeasureTheory.Integrable (fun u : ℝ =>
      logScaleBumpComplex cutoff u *
        Complex.exp ((u : ℂ) * (p.1 + p.2)) *
        Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2))) := by
  have hcont : Continuous (fun u : ℝ =>
      logScaleBumpComplex cutoff u *
        Complex.exp ((u : ℂ) * (p.1 + p.2)) *
        Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2))) := by
    have hb : Continuous (logScaleBumpComplex cutoff) :=
      (contDiff_logScaleBumpComplex cutoff).continuous
    have hp : Continuous (fun u : ℝ =>
        Complex.exp ((u : ℂ) * (p.1 + p.2))) := by fun_prop
    have hq : Continuous (fun u : ℝ =>
        Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2))) := by fun_prop
    exact (hb.mul hp).mul hq
  have hsupp : HasCompactSupport (fun u : ℝ =>
      logScaleBumpComplex cutoff u *
        Complex.exp ((u : ℂ) * (p.1 + p.2)) *
        Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2))) := by
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

noncomputable def logarithmicZeroStripFourthMoment
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) : ℂ :=
  ∫ u : ℝ, logScaleBumpComplex cutoff u *
    logarithmicZeroStripPairSum sigmaLower sigmaUpper T tau X u *
    starRingEnd ℂ
      (logarithmicZeroStripPairSum sigmaLower sigmaUpper T tau X u)

noncomputable def logarithmicZeroStripFourthNormMoment
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) : ℝ :=
  ∫ u : ℝ, logScaleBump cutoff u *
    ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 4

theorem logarithmicZeroStripFourthMoment_eq_ofReal_normMoment
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    logarithmicZeroStripFourthMoment cutoff
        sigmaLower sigmaUpper T tau X =
      (logarithmicZeroStripFourthNormMoment cutoff
        sigmaLower sigmaUpper T tau X : ℂ) := by
  unfold logarithmicZeroStripFourthMoment
    logarithmicZeroStripFourthNormMoment
  rw [← integral_complex_ofReal]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  rw [logarithmicZeroStripPairSum_eq_sq]
  change logScaleBumpComplex cutoff u *
      (logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u *
        logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) *
      star (logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u *
        logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) = _
  rw [mul_assoc]
  have hnorm :
      (logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u *
          logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) *
        star (logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u *
          logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) =
        (‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u *
          logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 2 : ℂ) :=
    RCLike.mul_conj _
  rw [hnorm]
  rw [norm_mul]
  simp only [logScaleBumpComplex, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem logarithmicZeroStripFourthNormMoment_nonneg
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    0 ≤ logarithmicZeroStripFourthNormMoment cutoff
      sigmaLower sigmaUpper T tau X := by
  unfold logarithmicZeroStripFourthNormMoment
  apply MeasureTheory.integral_nonneg
  intro u
  exact mul_nonneg (logScaleBump_nonneg cutoff u) (by positivity)

theorem norm_logarithmicZeroStripFourthMoment_eq_normMoment
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    ‖logarithmicZeroStripFourthMoment cutoff
      sigmaLower sigmaUpper T tau X‖ =
      logarithmicZeroStripFourthNormMoment cutoff
        sigmaLower sigmaUpper T tau X := by
  rw [logarithmicZeroStripFourthMoment_eq_ofReal_normMoment]
  simp [abs_of_nonneg (logarithmicZeroStripFourthNormMoment_nonneg cutoff
    sigmaLower sigmaUpper T tau X)]

private theorem star_exp_real_mul_pair (u : ℝ) (q : ℂ × ℂ) :
    starRingEnd ℂ (Complex.exp ((u : ℂ) * (q.1 + q.2))) =
      Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem logarithmicZeroStripFourthMoment_integrand_eq_pair_sum
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X u : ℝ) :
    logScaleBumpComplex cutoff u *
        logarithmicZeroStripPairSum sigmaLower sigmaUpper T tau X u *
        starRingEnd ℂ
          (logarithmicZeroStripPairSum sigmaLower sigmaUpper T tau X u) =
      ∑ p ∈ (zerosInRect sigmaLower sigmaUpper (-T) T ×ˢ
          zerosInRect sigmaLower sigmaUpper (-T) T),
        ∑ q ∈ (zerosInRect sigmaLower sigmaUpper (-T) T ×ˢ
            zerosInRect sigmaLower sigmaUpper (-T) T),
          (stripZeroPairCoefficient tau X p *
            starRingEnd ℂ (stripZeroPairCoefficient tau X q)) *
          (logScaleBumpComplex cutoff u *
            Complex.exp ((u : ℂ) * (p.1 + p.2)) *
            Complex.exp ((u : ℂ) * starRingEnd ℂ (q.1 + q.2))) := by
  classical
  unfold logarithmicZeroStripPairSum
  simp only [map_sum, map_mul]
  simp_rw [star_exp_real_mul_pair]
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem logarithmicZeroStripFourthMoment_eq_pair_sum
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    logarithmicZeroStripFourthMoment cutoff
        sigmaLower sigmaUpper T tau X =
      ∑ p ∈ (zerosInRect sigmaLower sigmaUpper (-T) T ×ˢ
          zerosInRect sigmaLower sigmaUpper (-T) T),
        ∑ q ∈ (zerosInRect sigmaLower sigmaUpper (-T) T ×ˢ
            zerosInRect sigmaLower sigmaUpper (-T) T),
          (stripZeroPairCoefficient tau X p *
            starRingEnd ℂ (stripZeroPairCoefficient tau X q)) *
          zeroPairPairFourierKernel cutoff p q := by
  classical
  unfold logarithmicZeroStripFourthMoment
  simp_rw [logarithmicZeroStripFourthMoment_integrand_eq_pair_sum]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [MeasureTheory.integral_const_mul]
      rw [← zeroPairPairFourierKernel_eq_integral]
    · intro q hq
      exact (integrable_zeroPairPairFourierKernel_integrand cutoff p q).const_mul _
  · intro p hp
    apply MeasureTheory.integrable_finsetSum _
    intro q hq
    exact (integrable_zeroPairPairFourierKernel_integrand cutoff p q).const_mul _

theorem norm_zeroPairPairFourierKernel_le
    (cutoff : GMSmoothCutoff) {K : ℝ}
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 4, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {p q : ℂ × ℂ}
    (hp1Lower : 0 ≤ p.1.re) (hp1Upper : p.1.re ≤ 1)
    (hp2Lower : 0 ≤ p.2.re) (hp2Upper : p.2.re ≤ 1)
    (hq1Lower : 0 ≤ q.1.re) (hq1Upper : q.1.re ≤ 1)
    (hq2Lower : 0 ≤ q.2.re) (hq2Upper : q.2.re ≤ 1) :
    ‖zeroPairPairFourierKernel cutoff p q‖ ≤
      K * zeroPairPairDecay p q := by
  have hs : p.1.re + p.2.re + q.1.re + q.2.re ∈ Set.Icc (0 : ℝ) 4 := by
    constructor <;> linarith
  have h := complexifiedLogScaleBumpFourier_norm_le_decay cutoff
    (hDecay (p.1.re + p.2.re + q.1.re + q.2.re) hs
      (zeroPairOrdinate p - zeroPairOrdinate q))
  simpa [zeroPairPairFourierKernel, zeroPairPairDecay] using h

theorem norm_stripZeroPairCoefficient_le
    {tau X sigmaUpper : ℝ} (htau : 0 < tau) (hX : 1 ≤ X)
    {p : ℂ × ℂ} (hp1Ne : p.1 ≠ 0) (hp2Ne : p.2 ≠ 0)
    (hp1Upper : p.1.re ≤ sigmaUpper) (hp2Upper : p.2.re ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    ‖stripZeroPairCoefficient tau X p‖ ≤
      ((zeroPairWeight p : ℝ) *
        ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau))) := by
  have h1 := norm_stripZeroCoefficient_le htau hX hp1Ne hp1Upper hsigmaUpper
  have h2 := norm_stripZeroCoefficient_le htau hX hp2Ne hp2Upper hsigmaUpper
  unfold stripZeroPairCoefficient zeroPairWeight
  rw [norm_mul]
  calc
    ‖stripZeroCoefficient tau X p.1‖ *
        ‖stripZeroCoefficient tau X p.2‖ ≤
      ((zeroMultiplicity p.1 : ℝ) * (X ^ sigmaUpper / tau)) *
        ((zeroMultiplicity p.2 : ℝ) * (X ^ sigmaUpper / tau)) := by gcongr
    _ = ((zeroMultiplicity p.1 * zeroMultiplicity p.2 : ℕ) : ℝ) *
        ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)) := by
      rw [Nat.cast_mul]
      ring

theorem stripZeroPairPairDecaySum_le
    {sigmaLower sigmaUpper T : ℝ} (hsigmaUpper : sigmaUpper ≤ 1) :
    (∑ p ∈ (zerosInRect sigmaLower sigmaUpper (-T) T ×ˢ
          zerosInRect sigmaLower sigmaUpper (-T) T),
        ∑ q ∈ (zerosInRect sigmaLower sigmaUpper (-T) T ×ˢ
            zerosInRect sigmaLower sigmaUpper (-T) T),
          (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
            zeroPairPairDecay p q) ≤
      zeroPairPairDecaySum sigmaLower T := by
  classical
  let strip := zerosInRect sigmaLower sigmaUpper (-T) T
  let full := zeroSet sigmaLower T
  let stripPairs := strip ×ˢ strip
  let fullPairs := full ×ˢ full
  have hsubset : strip ⊆ full := zerosInRect_strip_subset_zeroSet hsigmaUpper
  have hpairs : stripPairs ⊆ fullPairs := by
    intro p hp
    change p ∈ strip ×ˢ strip at hp
    rw [Finset.mem_product] at hp
    change p ∈ full ×ˢ full
    rw [Finset.mem_product]
    exact ⟨hsubset hp.1, hsubset hp.2⟩
  unfold zeroPairPairDecaySum zeroPairs
  change (∑ p ∈ stripPairs, ∑ q ∈ stripPairs,
      (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
        zeroPairPairDecay p q) ≤
    ∑ p ∈ fullPairs, ∑ q ∈ fullPairs,
      (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
        zeroPairPairDecay p q
  calc
    (∑ p ∈ stripPairs, ∑ q ∈ stripPairs,
        (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
          zeroPairPairDecay p q) ≤
      ∑ p ∈ stripPairs, ∑ q ∈ fullPairs,
        (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
          zeroPairPairDecay p q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg hpairs
      intro q hq hqnot
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (zeroPairPairDecay_nonneg p q)
    _ ≤ ∑ p ∈ fullPairs, ∑ q ∈ fullPairs,
        (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
          zeroPairPairDecay p q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hpairs
      intro p hp hpnot
      exact Finset.sum_nonneg (fun q hq => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (zeroPairPairDecay_nonneg p q))

/-- Complete finite analytic estimate in Gafni--Tao Lemma 2.4 before
substituting the additive-energy exponent and the physical height. -/
theorem norm_logarithmicZeroStripFourthMoment_le
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 4, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {sigmaLower sigmaUpper T tau X : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigmaLower)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (htau : 0 < tau) (hX : 1 ≤ X) :
    ‖logarithmicZeroStripFourthMoment cutoff
        sigmaLower sigmaUpper T tau X‖ ≤
      (K * (((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)) *
        ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)))) *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) *
          (zeroAdditiveEnergyCount sigmaLower T : ℝ)) := by
  classical
  let strip := zerosInRect sigmaLower sigmaUpper (-T) T
  let pairs := strip ×ˢ strip
  let R : ℝ := X ^ sigmaUpper / tau
  let R2 : ℝ := R * R
  have hsigmaLowerPos : 0 < sigmaLower :=
    lt_of_lt_of_le (by norm_num) hsigmaLower
  have hR : 0 ≤ R :=
    div_nonneg (Real.rpow_nonneg (by positivity) _) htau.le
  rw [logarithmicZeroStripFourthMoment_eq_pair_sum]
  calc
    ‖∑ p ∈ pairs, ∑ q ∈ pairs,
        (stripZeroPairCoefficient tau X p *
          starRingEnd ℂ (stripZeroPairCoefficient tau X q)) *
        zeroPairPairFourierKernel cutoff p q‖ ≤
      ∑ p ∈ pairs, ∑ q ∈ pairs,
        ‖(stripZeroPairCoefficient tau X p *
          starRingEnd ℂ (stripZeroPairCoefficient tau X q)) *
        zeroPairPairFourierKernel cutoff p q‖ := by
      exact norm_sum_le _ _ |>.trans (Finset.sum_le_sum fun p _ =>
        norm_sum_le _ _)
    _ ≤ ∑ p ∈ pairs, ∑ q ∈ pairs,
        (K * (R2 * R2)) *
          ((zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
            zeroPairPairDecay p q) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have hpMem : p ∈ strip ×ˢ strip := by simpa [pairs] using hp
      have hqMem : q ∈ strip ×ˢ strip := by simpa [pairs] using hq
      rw [Finset.mem_product] at hpMem hqMem
      have rectBounds {rho : ℂ} (hrho : rho ∈ strip) :
          sigmaLower ≤ rho.re ∧ rho.re ≤ sigmaUpper := by
        have hmem : rho ∈ zerosInRect sigmaLower sigmaUpper (-T) T := by
          simpa [strip] using hrho
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hmem
        have hb := (RiemannZeta.GuthMaynard.mem_ZeroRectangle
          sigmaLower sigmaUpper (-T) T rho).mp hmem.1
        exact ⟨hb.1, hb.2.1⟩
      have hp1Bounds := rectBounds hpMem.1
      have hp2Bounds := rectBounds hpMem.2
      have hq1Bounds := rectBounds hqMem.1
      have hq2Bounds := rectBounds hqMem.2
      have nonzero {rho : ℂ} (hrho : rho ∈ strip) : rho ≠ 0 := by
        apply ne_zero_of_mem_zerosInRect_of_pos hsigmaLowerPos
        simpa [strip] using hrho
      have hpCoeff := norm_stripZeroPairCoefficient_le htau hX
        (nonzero hpMem.1) (nonzero hpMem.2)
        hp1Bounds.2 hp2Bounds.2 hsigmaUpper
      have hqCoeff := norm_stripZeroPairCoefficient_le htau hX
        (nonzero hqMem.1) (nonzero hqMem.2)
        hq1Bounds.2 hq2Bounds.2 hsigmaUpper
      have hKernel := norm_zeroPairPairFourierKernel_le cutoff hDecay
        (hsigmaLowerPos.le.trans hp1Bounds.1)
        (hp1Bounds.2.trans hsigmaUpper)
        (hsigmaLowerPos.le.trans hp2Bounds.1)
        (hp2Bounds.2.trans hsigmaUpper)
        (hsigmaLowerPos.le.trans hq1Bounds.1)
        (hq1Bounds.2.trans hsigmaUpper)
        (hsigmaLowerPos.le.trans hq2Bounds.1)
        (hq2Bounds.2.trans hsigmaUpper)
      have hStarNorm :
          ‖starRingEnd ℂ (stripZeroPairCoefficient tau X q)‖ =
            ‖stripZeroPairCoefficient tau X q‖ := by
        change ‖star (stripZeroPairCoefficient tau X q)‖ =
          ‖stripZeroPairCoefficient tau X q‖
        exact norm_star _
      rw [norm_mul, norm_mul, hStarNorm]
      change ‖stripZeroPairCoefficient tau X p‖ *
          ‖stripZeroPairCoefficient tau X q‖ *
            ‖zeroPairPairFourierKernel cutoff p q‖ ≤ _
      calc
        ‖stripZeroPairCoefficient tau X p‖ *
            ‖stripZeroPairCoefficient tau X q‖ *
              ‖zeroPairPairFourierKernel cutoff p q‖ ≤
          ((zeroPairWeight p : ℝ) * R2) *
            ((zeroPairWeight q : ℝ) * R2) *
              (K * zeroPairPairDecay p q) := by gcongr
        _ = (K * (R2 * R2)) *
            ((zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
              zeroPairPairDecay p q) := by ring
    _ = (K * (R2 * R2)) *
        (∑ p ∈ pairs, ∑ q ∈ pairs,
          (zeroPairWeight p : ℝ) * (zeroPairWeight q : ℝ) *
            zeroPairPairDecay p q) := by
      simp only [Finset.mul_sum]
    _ ≤ (K * (R2 * R2)) * zeroPairPairDecaySum sigmaLower T := by
      apply mul_le_mul_of_nonneg_left
      · simpa [pairs, strip] using stripZeroPairPairDecaySum_le hsigmaUpper
      · exact mul_nonneg hK (mul_nonneg (mul_nonneg hR hR) (mul_nonneg hR hR))
    _ ≤ (K * (R2 * R2)) *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) *
          (zeroAdditiveEnergyCount sigmaLower T : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (zeroPairPairDecaySum_le_zeroAdditiveEnergyCount sigmaLower T)
        (mul_nonneg hK (mul_nonneg (mul_nonneg hR hR) (mul_nonneg hR hR)))
    _ = (K * (((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)) *
        ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)))) *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) *
          (zeroAdditiveEnergyCount sigmaLower T : ℝ)) := by rfl

/-- Composition of the actual additive-energy envelope with the paper's
physical height. -/
theorem zeroAdditiveEnergyEnvelope_at_explicitFormulaHeight
    {J theta sigma a : ℝ} (hJ : 0 < J) (htheta : theta < 1)
    (ha : 0 ≤ a) (hsigma : sigma ≤ 1)
    (hEnergy : ZeroAdditiveEnergyEnvelope sigma a) :
    EpsilonExponentBound
      (fun X => (zeroAdditiveEnergyCount sigma
        (explicitFormulaHeight J theta X) : ℝ))
      ((1 - theta) * (a * (1 - sigma))) := by
  let r : ℝ := 1 - theta
  let d : ℝ := a * (1 - sigma)
  have hr : 0 < r := sub_pos.mpr htheta
  have hd : 0 ≤ d := mul_nonneg ha (sub_nonneg.mpr hsigma)
  unfold ZeroAdditiveEnergyEnvelope at hEnergy
  unfold EpsilonExponentBound at hEnergy ⊢
  intro eps heps
  let eta : ℝ := min 1 (eps / (2 * (r + d + 1)))
  have hsum : 0 < r + d + 1 := by linarith
  have heta : 0 < eta :=
    lt_min zero_lt_one (div_pos heps (mul_pos two_pos hsum))
  have hetaBudget : eta * (r + d + 1) ≤ eps / 2 := by
    have hEtaLe : eta ≤ eps / (2 * (r + d + 1)) := min_le_right _ _
    calc
      eta * (r + d + 1) ≤
          (eps / (2 * (r + d + 1))) * (r + d + 1) := by gcongr
      _ = eps / 2 := by field_simp
  have hExponent : (r + eta) * (d + eta) ≤ r * d + eps := by
    have hetaNonneg : 0 ≤ eta := heta.le
    have hetaOne : eta ≤ 1 := min_le_left _ _
    nlinarith
  have hComposed :=
    (hEnergy eta heta).comp_tendsto
      (tendsto_explicitFormulaHeight_atTop hJ htheta)
  have hCompare :
      (fun X : ℝ =>
          explicitFormulaHeight J theta X ^ eta *
            |explicitFormulaHeight J theta X ^ d|) =O[atTop]
        (fun X : ℝ => X ^ eps * |X ^ (r * d)|) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_explicitFormulaHeight_le_rpow
        (J := J) (theta := theta) heta,
      eventually_ge_atTop (Real.exp 1)] with X hHeightLe hX
    have hXPos : 0 < X := (Real.exp_pos 1).trans_le hX
    have hExpOne : (1 : ℝ) < Real.exp 1 := by
      have h : Real.exp 0 < Real.exp 1 := Real.exp_lt_exp.mpr zero_lt_one
      simpa only [Real.exp_zero] using h
    have hXOne : 1 ≤ X := hExpOne.le.trans hX
    have hHeightPos : 0 < explicitFormulaHeight J theta X :=
      explicitFormulaHeight_pos hJ (hExpOne.trans_le hX)
    have hPower : 0 ≤ d + eta := add_nonneg hd heta.le
    have hHeightPower :
        explicitFormulaHeight J theta X ^ (d + eta) ≤
          X ^ ((r + eta) * (d + eta)) := by
      calc
        explicitFormulaHeight J theta X ^ (d + eta) ≤
            (X ^ (r + eta)) ^ (d + eta) :=
          Real.rpow_le_rpow hHeightPos.le hHeightLe hPower
        _ = X ^ ((r + eta) * (d + eta)) :=
          (Real.rpow_mul hXPos.le _ _).symm
    have hToTarget : X ^ ((r + eta) * (d + eta)) ≤
        X ^ (r * d + eps) :=
      Real.rpow_le_rpow_of_exponent_le hXOne hExponent
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hHeightPos.le eta)
        (abs_nonneg _)), one_mul,
      abs_of_nonneg (Real.rpow_nonneg hHeightPos.le d),
      ← Real.rpow_add hHeightPos,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hXPos.le eps)
        (abs_nonneg _)),
      abs_of_nonneg (Real.rpow_nonneg hXPos.le (r * d)),
      ← Real.rpow_add hXPos]
    simpa only [add_comm] using hHeightPower.trans hToTarget
  simpa only [Function.comp_def, r, d, mul_assoc] using hComposed.trans hCompare

theorem integrable_logarithmicZeroStripFourthNormMoment_integrand
    (cutoff : GMSmoothCutoff)
    (sigmaLower sigmaUpper T tau X : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ => logScaleBump cutoff u *
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 4) := by
  have hsum : Continuous (fun u : ℝ =>
      logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) := by
    unfold logarithmicZeroStripSum
    fun_prop
  have hcont : Continuous (fun u : ℝ => logScaleBump cutoff u *
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 4) :=
    (contDiff_logScaleBump cutoff).continuous.mul (hsum.norm.pow 4)
  have hsupp : HasCompactSupport (fun u : ℝ => logScaleBump cutoff u *
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 4) := by
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

noncomputable def zeroStripPhysicalFourthMoment
    (sigmaLower sigmaUpper T tau X : ℝ) : ℝ :=
  (1 / X) * ∫ x : ℝ in X..2 * X,
    ‖zeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ^ 4

theorem zeroStripPhysicalFourthMoment_eq_logarithmic
    {sigmaLower sigmaUpper T tau X : ℝ}
    (htau : 0 < tau) (hX : 0 < X) :
    zeroStripPhysicalFourthMoment sigmaLower sigmaUpper T tau X =
      ∫ u : ℝ in 0..Real.log 2,
        ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 4 *
          Real.exp u := by
  let g : ℝ → ℝ := fun x =>
    ‖zeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ^ 4
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
  unfold zeroStripPhysicalFourthMoment
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
      (X * Real.exp u)‖ ^ 4 * Real.exp u = _
  rw [zeroStripIncrementSum_mul_exp_eq_logarithmicZeroStripSum htau hX.le]

theorem zeroStripPhysicalFourthMoment_le_logarithmicNormMoment
    (cutoff : GMSmoothCutoff)
    {sigmaLower sigmaUpper T tau X : ℝ}
    (htau : 0 < tau) (hX : 0 < X) :
    zeroStripPhysicalFourthMoment sigmaLower sigmaUpper T tau X ≤
      2 * logarithmicZeroStripFourthNormMoment cutoff
        sigmaLower sigmaUpper T tau X := by
  let q : ℝ → ℝ := fun u =>
    ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 4
  have hsum : Continuous (fun u : ℝ =>
      logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u) := by
    unfold logarithmicZeroStripSum
    fun_prop
  have hq : Continuous q := hsum.norm.pow 4
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
    nlinarith [show 0 ≤ q u by dsimp [q]; positivity]
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
        logarithmicZeroStripFourthNormMoment cutoff
          sigmaLower sigmaUpper T tau X := by
    rw [hRestricted]
    unfold logarithmicZeroStripFourthNormMoment
    exact MeasureTheory.setIntegral_le_integral
      (integrable_logarithmicZeroStripFourthNormMoment_integrand cutoff
        sigmaLower sigmaUpper T tau X)
      (Filter.Eventually.of_forall fun u =>
        mul_nonneg (logScaleBump_nonneg cutoff u) (by positivity))
  rw [zeroStripPhysicalFourthMoment_eq_logarithmic htau hX]
  change (∫ u : ℝ in 0..Real.log 2, q u * Real.exp u) ≤ _
  calc
    (∫ u : ℝ in 0..Real.log 2, q u * Real.exp u) ≤
        ∫ u : ℝ in 0..Real.log 2, 2 * q u := hInterval
    _ = 2 * ∫ u : ℝ in 0..Real.log 2, q u := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 2 * logarithmicZeroStripFourthNormMoment cutoff
        sigmaLower sigmaUpper T tau X := by gcongr

theorem zeroStripPhysicalFourthMoment_le_count
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 4, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {sigmaLower sigmaUpper T tau X : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigmaLower)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (htau : 0 < tau) (hX : 1 ≤ X) :
    zeroStripPhysicalFourthMoment sigmaLower sigmaUpper T tau X ≤
      2 * ((K * (((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)) *
        ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)))) *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) *
          (zeroAdditiveEnergyCount sigmaLower T : ℝ))) := by
  calc
    zeroStripPhysicalFourthMoment sigmaLower sigmaUpper T tau X ≤
        2 * logarithmicZeroStripFourthNormMoment cutoff
          sigmaLower sigmaUpper T tau X :=
      zeroStripPhysicalFourthMoment_le_logarithmicNormMoment cutoff
        htau (zero_lt_one.trans_le hX)
    _ = 2 * ‖logarithmicZeroStripFourthMoment cutoff
        sigmaLower sigmaUpper T tau X‖ := by
      rw [norm_logarithmicZeroStripFourthMoment_eq_normMoment]
    _ ≤ 2 * ((K * (((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)) *
        ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)))) *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) *
          (zeroAdditiveEnergyCount sigmaLower T : ℝ))) := by
      gcongr
      exact norm_logarithmicZeroStripFourthMoment_le cutoff hK hDecay
        hsigmaLower hsigmaUpper htau hX

noncomputable def zeroStripFourthPhysicalMajorant
    (J theta sigmaLower sigmaUpper X : ℝ) : ℝ :=
  ((X ^ (theta + sigmaUpper - 1) * X ^ (theta + sigmaUpper - 1)) *
    (X ^ (theta + sigmaUpper - 1) * X ^ (theta + sigmaUpper - 1))) *
      (zeroAdditiveEnergyCount sigmaLower
        (explicitFormulaHeight J theta X) : ℝ)

theorem zeroStripFourthPhysicalMajorant_epsilonBound
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (htheta : theta < 1) (ha : 0 ≤ a)
    (hsigmaLower : sigmaLower ≤ 1)
    (hEnergy : ZeroAdditiveEnergyEnvelope sigmaLower a) :
    EpsilonExponentBound
      (zeroStripFourthPhysicalMajorant J theta sigmaLower sigmaUpper)
      ((1 - theta) * (a * (1 - sigmaLower)) +
        4 * theta + 4 * sigmaUpper - 4) := by
  let d : ℝ := (1 - theta) * (a * (1 - sigmaLower))
  let s : ℝ := theta + sigmaUpper - 1
  have hCount := zeroAdditiveEnergyEnvelope_at_explicitFormulaHeight
    hJ htheta ha hsigmaLower hEnergy
  unfold EpsilonExponentBound at hCount ⊢
  have hScaled :=
    RiemannZeta.GuthMaynard.EpsilonPowerBound.mul_left_rpow
      hCount (4 * s)
  intro eps heps
  have h := hScaled eps heps
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    unfold zeroStripFourthPhysicalMajorant
    have hPow :
        ((X ^ s * X ^ s) * (X ^ s * X ^ s)) = X ^ (4 * s) := by
      have hTwo : X ^ s * X ^ s = X ^ (2 * s) := by
        rw [← Real.rpow_add hX]
        congr 1
        ring
      rw [hTwo, ← Real.rpow_add hX]
      congr 1
      ring
    simp [s, hPow]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hPow : X ^ (4 * s) * X ^ d =
        X ^ (d + 4 * theta + 4 * sigmaUpper - 4) := by
      rw [← Real.rpow_add hX]
      congr 1
      dsimp [s]
      ring
    rw [hPow]

theorem zeroStripPhysicalFourthMoment_nonneg
    {sigmaLower sigmaUpper T tau X : ℝ} (hX : 0 < X) :
    0 ≤ zeroStripPhysicalFourthMoment sigmaLower sigmaUpper T tau X := by
  unfold zeroStripPhysicalFourthMoment
  apply mul_nonneg (one_div_nonneg.mpr hX.le)
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x hx
  positivity

theorem zeroStripPhysicalFourthMoment_le_majorant
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 4, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {J theta sigmaLower sigmaUpper X : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigmaLower)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hX : 1 ≤ X) :
    zeroStripPhysicalFourthMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X ≤
      (2 * K * (3 ^ (10 : ℕ) * integerBinDecayMass)) *
        zeroStripFourthPhysicalMajorant J theta sigmaLower sigmaUpper X := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hFinite := zeroStripPhysicalFourthMoment_le_count cutoff hK hDecay
    (T := explicitFormulaHeight J theta X) (tau := localTau X theta)
    (X := X) hsigmaLower hsigmaUpper (localTau_pos hXPos) hX
  have hScale : X ^ sigmaUpper / localTau X theta =
      X ^ (theta + sigmaUpper - 1) := rpow_div_localTau hXPos
  unfold zeroStripFourthPhysicalMajorant
  calc
    zeroStripPhysicalFourthMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X ≤
      2 * ((K *
        ((X ^ (theta + sigmaUpper - 1) * X ^ (theta + sigmaUpper - 1)) *
          (X ^ (theta + sigmaUpper - 1) * X ^ (theta + sigmaUpper - 1)))) *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) *
          (zeroAdditiveEnergyCount sigmaLower
            (explicitFormulaHeight J theta X) : ℝ))) := by
      simpa only [hScale] using hFinite
    _ = (2 * K * (3 ^ (10 : ℕ) * integerBinDecayMass)) *
        (((X ^ (theta + sigmaUpper - 1) * X ^ (theta + sigmaUpper - 1)) *
          (X ^ (theta + sigmaUpper - 1) * X ^ (theta + sigmaUpper - 1))) *
          (zeroAdditiveEnergyCount sigmaLower
            (explicitFormulaHeight J theta X) : ℝ)) := by ring

/-- Full source-form Gafni--Tao Lemma 2.4.  It consumes the actual finite
four-zero tolerance-one count with product analytic multiplicity. -/
theorem zeroStripPhysicalFourthMoment_epsilonBound
    (cutoff : GMSmoothCutoff)
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (htheta : theta < 1) (ha : 0 ≤ a)
    (hsigmaLower : 1 / 2 ≤ sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hEnergy : ZeroAdditiveEnergyEnvelope sigmaLower a) :
    EpsilonExponentBound
      (fun X => zeroStripPhysicalFourthMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X)
      ((1 - theta) * (a * (1 - sigmaLower)) +
        4 * theta + 4 * sigmaUpper - 4) := by
  obtain ⟨K, hK, hDecay⟩ :=
    exists_quarticComplexifiedLogScaleBumpFourier_tenfold_decay cutoff
  let C : ℝ := 2 * K * (3 ^ (10 : ℕ) * integerBinDecayMass)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by positivity) hK)
      (mul_nonneg (by positivity) integerBinDecayMass_nonneg)
  have hDomination :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (fun X => zeroStripPhysicalFourthMoment sigmaLower sigmaUpper
          (explicitFormulaHeight J theta X) (localTau X theta) X)
        (zeroStripFourthPhysicalMajorant J theta sigmaLower sigmaUpper) := by
    intro eps heps
    have hFixed :
        (fun X : ℝ =>
          |zeroStripPhysicalFourthMoment sigmaLower sigmaUpper
            (explicitFormulaHeight J theta X) (localTau X theta) X|) =O[atTop]
          (fun X : ℝ =>
            |zeroStripFourthPhysicalMajorant J theta
              sigmaLower sigmaUpper X|) := by
      apply IsBigO.of_bound C
      filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
      have hExpOne : 1 < Real.exp 1 := by
        simpa only [Real.exp_zero] using
          Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1)
      have hXOne : 1 ≤ X := hExpOne.le.trans hX
      have hXPos : 0 < X := zero_lt_one.trans hExpOne |>.trans_le hX
      have hPoint := zeroStripPhysicalFourthMoment_le_majorant
        (J := J) (theta := theta) cutoff hK hDecay
        hsigmaLower hsigmaUpper hXOne
      have hMajorantNonneg :
          0 ≤ zeroStripFourthPhysicalMajorant J theta
            sigmaLower sigmaUpper X := by
        unfold zeroStripFourthPhysicalMajorant
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hXPos.le _)
              (Real.rpow_nonneg hXPos.le _))
            (mul_nonneg (Real.rpow_nonneg hXPos.le _)
              (Real.rpow_nonneg hXPos.le _))) (by positivity)
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg
        (zeroStripPhysicalFourthMoment_nonneg hXPos), Real.norm_eq_abs,
        abs_abs, abs_of_nonneg hMajorantNonneg]
      simpa [C] using hPoint
    exact hFixed.trans
      ((RiemannZeta.GuthMaynard.EpsilonPowerBound.refl
        (zeroStripFourthPhysicalMajorant J theta sigmaLower sigmaUpper))
          eps heps)
  exact hDomination.trans
    (zeroStripFourthPhysicalMajorant_epsilonBound hJ htheta ha
      (hsigmaOrder.trans hsigmaUpper) hEnergy)

end GafniTao

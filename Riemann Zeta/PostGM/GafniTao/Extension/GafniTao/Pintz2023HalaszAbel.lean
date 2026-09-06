import GafniTao.Pintz2023CorollaryThree
import GafniTao.Pintz2023HalaszKernelBounds
import RiemannZeta.GuthMaynard.MediumTypeIEndpoint

/-!
# Pintz (2023), the two Abel transfers after equation (4.21)

The Gram entry in (4.19) contains the extra factor `n^(4 * eta)`, whereas
Corollaries 2 and 3 estimate the block with exponent
`xi = eta_nu + eta_kappa`.  This file inserts that factor by an exact
increasing-weight Abel summation.  A second Abel summation inserts the literal
Halasz kernel.  Below the ambient scale it retains the source saving `R/N`
from (4.22); on an arbitrary block it retains the two exponential endpoints.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Reindex the literal weighted block to a range starting at zero. -/
theorem pintz2023WeightedBlock_eq_shifted_range
    (xi : ℝ) (L j : ℕ) (t : ℝ) :
    pintz2023WeightedBlock xi L (L + j) t =
      ∑ i ∈ Finset.range j,
        ((L + 1 + i : ℕ) : ℝ) ^ (-(1 - xi)) •
          (L + 1 + i : ℂ) ^ (-(t : ℂ) * I) := by
  unfold pintz2023WeightedBlock
  have hIoc : Finset.Ioc L (L + j) =
      Finset.Ico (L + 1) (L + j + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : L + j + 1 - (L + 1) = j := by omega
  rw [hLength]
  simp only [Nat.cast_add, Nat.cast_one]

/-- The factor `n^a` shifts Pintz's weighted exponent from `xi` to
`xi + a`, term by term. -/
theorem pintz2023_weighted_term_shift
    {n : ℕ} (hn : 0 < n) (xi a t : ℝ) :
    (n : ℝ) ^ a •
        ((n : ℝ) ^ (-(1 - xi)) • (n : ℂ) ^ (-(t : ℂ) * I)) =
      (n : ℝ) ^ (-(1 - (xi + a))) •
        (n : ℂ) ^ (-(t : ℂ) * I) := by
  rw [smul_smul]
  congr 1
  rw [← Real.rpow_add (by positivity : (0 : ℝ) < n)]
  congr 1
  ring

/-- Exact increasing-weight Abel transfer for the `n^a` factor.  The input
is a uniform bound for every source prefix `(L,L+j]`. -/
theorem norm_pintz2023WeightedBlock_shift_le_of_prefix
    {xi a t B : ℝ} {L R : ℕ}
    (hL : 0 < L) (hLR : L < R) (ha : 0 ≤ a)
    (hpartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤ B) :
    ‖pintz2023WeightedBlock (xi + a) L R t‖ ≤
      2 * (R : ℝ) ^ a * B := by
  let M : ℕ := R - L
  let f : ℕ → ℝ := fun i => ((L + 1 + i : ℕ) : ℝ) ^ a
  let g : ℕ → ℂ := fun i =>
    ((L + 1 + i : ℕ) : ℝ) ^ (-(1 - xi)) •
      (L + 1 + i : ℂ) ^ (-(t : ℂ) * I)
  have hM : 0 < M := by
    dsimp only [M]
    omega
  have hLR' : L + M = R := by
    dsimp only [M]
    omega
  have hf : ∀ i, i < M → 0 ≤ f i := by
    intro i hi
    exact Real.rpow_nonneg (by positivity) _
  have hmono : ∀ i, i + 1 < M → f i ≤ f (i + 1) := by
    intro i hi
    dsimp only [f]
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast Nat.le_succ (L + 1 + i)
    · exact ha
  have hpartial' : ∀ j, j ≤ M →
      ‖∑ i ∈ Finset.range j, g i‖ ≤ B := by
    intro j hj
    simpa only [g, pintz2023WeightedBlock_eq_shifted_range] using
      hpartial j (by simpa only [M] using hj)
  have hAbel :=
    RiemannZeta.GuthMaynard.norm_weighted_sum_le_of_monotone
      f g M B hM hf hmono hpartial'
  have hLast : L + 1 + (M - 1) = R := by omega
  have hIdentity :
      (∑ i ∈ Finset.range M, f i • g i) =
        pintz2023WeightedBlock (xi + a) L R t := by
    rw [← hLR', pintz2023WeightedBlock_eq_shifted_range]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f, g]
    simp only [Nat.cast_add, Nat.cast_one]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (pintz2023_weighted_term_shift (n := L + 1 + i) (by omega) xi a t)
  rw [hIdentity] at hAbel
  simpa only [f, hLast] using hAbel

/-- Corollary 3 with the `n^(4 eta)` factor from the Gram vector restored by
the preceding exact Abel transfer.  Corollary 3 itself is still invoked at
`xi`, exactly as in Pintz (4.21). -/
theorem pintz2023_corollary_three_shift_four_eta
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (xi eta : ℝ) (L R : ℕ) (t T : ℝ),
      0 ≤ eta →
      xi ≤ pintz2023HBAlpha r - 6 * epsilon →
      0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon →
      0 < L → L < R → R ≤ 2 * L →
      0 < t → t ≤ T → 1 ≤ T →
      pintz2023CriticalScale r xi epsilon T ≤ (L : ℝ) →
      (L : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
      ‖pintz2023WeightedBlock (xi + 4 * eta) L R t‖ ≤
        C * (R : ℝ) ^ (4 * eta) * (L : ℝ) ^ (-3 * epsilon) := by
  obtain ⟨C₀, hC₀, hCor⟩ :=
    pintz2023_corollary_three_native r epsilon B hr hepsilon hB
  refine ⟨2 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro xi eta L R t T heta hxi hden hL hLR hR ht htT hT hcritical hscale
  apply (norm_pintz2023WeightedBlock_shift_le_of_prefix
    (xi := xi) (a := 4 * eta) (t := t)
    (B := C₀ * (L : ℝ) ^ (-3 * epsilon)) hL hLR (by positivity) ?_).trans_eq
  · ring
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [pintz2023WeightedBlock]
      positivity
    · have hLj : L < L + j := by omega
      have hLjR : L + j ≤ R := by omega
      exact hCor xi L (L + j) t T hxi hden hL hLj
        (hLjR.trans hR) ht htT hT hcritical hscale

/-- The elementary numerical inequality locating the increasing side of the
Halasz kernel. -/
theorem one_half_le_exp_neg_one_half :
    (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
  have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
  norm_num at h ⊢
  exact h

/-- On integer arguments up to the ambient scale, the literal kernel in
(4.18) is increasing.  This is the monotonicity used together with (4.22),
not an unspecified smooth-weight estimate. -/
theorem pintz2023HalaszKernel_mono_of_succ_le
    {N n : ℕ} (hN : 0 < N) (hn : n + 1 ≤ N) :
    pintz2023HalaszKernel N n ≤ pintz2023HalaszKernel N (n + 1) := by
  let p : ℝ := Real.exp (-(n : ℝ) / (2 * N))
  let q : ℝ := Real.exp (-((n + 1 : ℕ) : ℝ) / (2 * N))
  have hden : (0 : ℝ) < 2 * N := by positivity
  have hqHalf : (1 / 2 : ℝ) ≤ q := by
    have hexp : -(1 / 2 : ℝ) ≤ -((n + 1 : ℕ) : ℝ) / (2 * N) := by
      rw [le_div_iff₀ hden]
      have hnReal : (((n + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast hn
      push_cast
      norm_num at hnReal ⊢
      linarith
    exact one_half_le_exp_neg_one_half.trans
      (Real.exp_le_exp.mpr hexp)
  have hqp : q ≤ p := by
    apply Real.exp_le_exp.mpr
    dsimp only [p, q]
    rw [div_le_div_iff₀ hden hden]
    push_cast
    linarith
  have hdiff : 0 ≤ (p - q) * (p + q - 1) := by
    exact mul_nonneg (sub_nonneg.mpr hqp) (by linarith)
  rw [pintz2023HalaszKernel_factor hN,
    pintz2023HalaszKernel_factor hN]
  change p * (1 - p) ≤ q * (1 - q)
  nlinarith

/-- One finite block of the exact smoothed Gram series. -/
noncomputable def pintz2023HalaszKernelWeightedBlock
    (N : ℕ) (xi : ℝ) (L R : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc L R,
    pintz2023HalaszKernel N n •
      ((n : ℝ) ^ (-(1 - xi)) • (n : ℂ) ^ (-(t : ℂ) * I))

theorem pintz2023HalaszKernelWeightedBlock_eq_shifted_range
    (N : ℕ) (xi : ℝ) (L j : ℕ) (t : ℝ) :
    pintz2023HalaszKernelWeightedBlock N xi L (L + j) t =
      ∑ i ∈ Finset.range j,
        pintz2023HalaszKernel N (L + 1 + i) •
          (((L + 1 + i : ℕ) : ℝ) ^ (-(1 - xi)) •
            (L + 1 + i : ℂ) ^ (-(t : ℂ) * I)) := by
  unfold pintz2023HalaszKernelWeightedBlock
  have hIoc : Finset.Ioc L (L + j) =
      Finset.Ico (L + 1) (L + j + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : L + j + 1 - (L + 1) = j := by omega
  rw [hLength]
  simp only [Nat.cast_add, Nat.cast_one]

/-- Exact second Abel transfer below the ambient scale.  Combining kernel
monotonicity with (4.22) produces the literal factor `R/N` used in (4.23). -/
theorem norm_pintz2023HalaszKernelWeightedBlock_le_div_of_prefix
    {N L R : ℕ} {xi t B : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hLR : L < R) (hRN : R ≤ N)
    (hpartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤ B) :
    ‖pintz2023HalaszKernelWeightedBlock N xi L R t‖ ≤
      ((R : ℝ) / N) * B := by
  let M : ℕ := R - L
  let f : ℕ → ℝ := fun i => pintz2023HalaszKernel N (L + 1 + i)
  let g : ℕ → ℂ := fun i =>
    ((L + 1 + i : ℕ) : ℝ) ^ (-(1 - xi)) •
      (L + 1 + i : ℂ) ^ (-(t : ℂ) * I)
  have hM : 0 < M := by dsimp only [M]; omega
  have hLM : L + M = R := by dsimp only [M]; omega
  have hf : ∀ i, i < M → 0 ≤ f i := by
    intro i hi
    exact (pintz2023HalaszKernel_pos hN (by omega)).le
  have hmono : ∀ i, i + 1 < M → f i ≤ f (i + 1) := by
    intro i hi
    dsimp only [f]
    exact pintz2023HalaszKernel_mono_of_succ_le hN (by omega)
  have hpartial' : ∀ j, j ≤ M →
      ‖∑ i ∈ Finset.range j, g i‖ ≤ B := by
    intro j hj
    simpa only [g, pintz2023WeightedBlock_eq_shifted_range] using
      hpartial j (by simpa only [M] using hj)
  have hAbel :=
    RiemannZeta.GuthMaynard.norm_weighted_sum_le_of_monotone
      f g M B hM hf hmono hpartial'
  have hLast : L + 1 + (M - 1) = R := by omega
  have hIdentity :
      (∑ i ∈ Finset.range M, f i • g i) =
        pintz2023HalaszKernelWeightedBlock N xi L R t := by
    rw [← hLM, pintz2023HalaszKernelWeightedBlock_eq_shifted_range]
  rw [hIdentity] at hAbel
  have hKernel := pintz2023HalaszKernel_le_div (N := N) (n := R) hN
  calc
    ‖pintz2023HalaszKernelWeightedBlock N xi L R t‖ ≤
        2 * pintz2023HalaszKernel N R * B := by
      simpa only [f, hLast] using hAbel
    _ ≤ 2 * ((R : ℝ) / (2 * N)) * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKernel (by norm_num))
        (by
          have := hpartial 0 (Nat.zero_le _)
          simpa [pintz2023WeightedBlock] using this)
    _ = ((R : ℝ) / N) * B := by ring

/-- The two source weights can be inserted successively below the ambient
scale.  This is the exact formal counterpart of using (4.21)/(4.23) after
extracting the `n^(4 eta)` factor from the Gram entry. -/
theorem norm_pintz2023HalaszKernelWeightedBlock_shift_le_of_prefix
    {N L R : ℕ} {xi a t B : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hLR : L < R) (hRN : R ≤ N)
    (ha : 0 ≤ a)
    (hpartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤ B) :
    ‖pintz2023HalaszKernelWeightedBlock N (xi + a) L R t‖ ≤
      2 * ((R : ℝ) / N) * (R : ℝ) ^ a * B := by
  have hB : 0 ≤ B := by
    have hzero := hpartial 0 (Nat.zero_le _)
    simpa [pintz2023WeightedBlock] using hzero
  have hShifted : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock (xi + a) L (L + j) t‖ ≤
        2 * (R : ℝ) ^ a * B := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [pintz2023WeightedBlock]
      positivity
    · have hLj : L < L + j := by omega
      have hLjR : L + j ≤ R := by omega
      have hShift := norm_pintz2023WeightedBlock_shift_le_of_prefix
        hL hLj ha (fun q hq => hpartial q (by omega))
      have hbase : (0 : ℝ) ≤ ((L + j : ℕ) : ℝ) := Nat.cast_nonneg _
      have hbaseLe : ((L + j : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hLjR
      have hpow : ((L + j : ℕ) : ℝ) ^ a ≤ (R : ℝ) ^ a :=
        Real.rpow_le_rpow hbase hbaseLe ha
      exact hShift.trans (by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) hB)
  have hKernel :=
    norm_pintz2023HalaszKernelWeightedBlock_le_div_of_prefix
      hN hL hLR hRN hShifted
  calc
    ‖pintz2023HalaszKernelWeightedBlock N (xi + a) L R t‖ ≤
        ((R : ℝ) / N) * (2 * (R : ℝ) ^ a * B) := hKernel
    _ = 2 * ((R : ℝ) / N) * (R : ℝ) ^ a * B := by ring

/-- One exponentially damped block.  The Halasz kernel is the difference of
the instances with scales `2N` and `N`. -/
noncomputable def pintz2023ExponentialWeightedBlock
    (C : ℝ) (xi : ℝ) (L R : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc L R,
    Real.exp (-(n : ℝ) / C) •
      ((n : ℝ) ^ (-(1 - xi)) • (n : ℂ) ^ (-(t : ℂ) * I))

/-- Antitone Abel summation inserts one of the two literal exponentials while
retaining its left-endpoint decay. -/
theorem norm_pintz2023ExponentialWeightedBlock_le_of_prefix
    {C xi t B : ℝ} {L R : ℕ}
    (hC : 0 < C) (hLR : L < R)
    (hpartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤ B) :
    ‖pintz2023ExponentialWeightedBlock C xi L R t‖ ≤
      Real.exp (-((L + 1 : ℕ) : ℝ) / C) * B := by
  unfold pintz2023ExponentialWeightedBlock
  apply ford_norm_weighted_Ioc_le_of_antitone
      (fun n => Real.exp (-(n : ℝ) / C))
      (fun n => (n : ℝ) ^ (-(1 - xi)) •
        (n : ℂ) ^ (-(t : ℂ) * I)) L R B hLR
  · intro n hn
    exact (Real.exp_pos _).le
  · intro n hnL hnR
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hC.le
    push_cast
    linarith
  · intro j hj
    simpa only [pintz2023WeightedBlock_eq_shifted_range,
      Nat.cast_add, Nat.cast_one] using hpartial j hj

/-- Exact decomposition of a kernel-weighted block into its two exponential
pieces. -/
theorem pintz2023HalaszKernelWeightedBlock_eq_exp_sub_exp
    (N : ℕ) (xi : ℝ) (L R : ℕ) (t : ℝ) :
    pintz2023HalaszKernelWeightedBlock N xi L R t =
      pintz2023ExponentialWeightedBlock (2 * N) xi L R t -
        pintz2023ExponentialWeightedBlock N xi L R t := by
  unfold pintz2023HalaszKernelWeightedBlock
    pintz2023ExponentialWeightedBlock pintz2023HalaszKernel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sub_smul]

/-- Arbitrary-block kernel insertion.  Unlike the small-block form, this
version is valid on either side of the kernel maximum and keeps the exact two
exponential endpoint factors needed for the far-tail sum. -/
theorem norm_pintz2023HalaszKernelWeightedBlock_le_exp_of_prefix
    {N L R : ℕ} {xi t B : ℝ}
    (hN : 0 < N) (hLR : L < R)
    (hpartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤ B) :
    ‖pintz2023HalaszKernelWeightedBlock N xi L R t‖ ≤
      (Real.exp (-((L + 1 : ℕ) : ℝ) / (2 * N)) +
        Real.exp (-((L + 1 : ℕ) : ℝ) / N)) * B := by
  have hTwoN : (0 : ℝ) < 2 * N := by positivity
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hFirst := norm_pintz2023ExponentialWeightedBlock_le_of_prefix
    hTwoN hLR hpartial
  have hSecond := norm_pintz2023ExponentialWeightedBlock_le_of_prefix
    hNReal hLR hpartial
  rw [pintz2023HalaszKernelWeightedBlock_eq_exp_sub_exp]
  calc
    ‖pintz2023ExponentialWeightedBlock (2 * N) xi L R t -
        pintz2023ExponentialWeightedBlock N xi L R t‖ ≤
      ‖pintz2023ExponentialWeightedBlock (2 * N) xi L R t‖ +
        ‖pintz2023ExponentialWeightedBlock N xi L R t‖ := norm_sub_le _ _
    _ ≤ Real.exp (-((L + 1 : ℕ) : ℝ) / (2 * N)) * B +
        Real.exp (-((L + 1 : ℕ) : ℝ) / N) * B :=
      add_le_add hFirst hSecond
    _ = _ := by ring

#print axioms pintz2023WeightedBlock_eq_shifted_range
#print axioms pintz2023_weighted_term_shift
#print axioms norm_pintz2023WeightedBlock_shift_le_of_prefix
#print axioms pintz2023_corollary_three_shift_four_eta
#print axioms pintz2023HalaszKernel_mono_of_succ_le
#print axioms norm_pintz2023HalaszKernelWeightedBlock_le_div_of_prefix
#print axioms norm_pintz2023HalaszKernelWeightedBlock_shift_le_of_prefix
#print axioms norm_pintz2023ExponentialWeightedBlock_le_of_prefix
#print axioms pintz2023HalaszKernelWeightedBlock_eq_exp_sub_exp
#print axioms norm_pintz2023HalaszKernelWeightedBlock_le_exp_of_prefix

end

end GafniTao

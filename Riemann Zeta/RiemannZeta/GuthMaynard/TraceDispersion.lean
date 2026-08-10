import Mathlib.Algebra.Order.Chebyshev
import RiemannZeta.GuthMaynard.LargeValuesMatrix

open Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Sixth-moment trace dispersion

The first lemma is the nonnegativity assertion needed for the sixth root in
Guth--Maynard Lemma 4.2.  It is a direct finite Jensen inequality, proved here
over the reals before the spectral specialization.
-/

theorem sixthMoment_dispersion_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (hs : s.Nonempty) :
    0 ≤ (∑ i ∈ s, x i ^ 6) -
      (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 2 := by
  have hJensen := pow_sum_le_card_mul_sum_pow
    (s := s) (f := fun i => x i ^ 2) (fun i hi => sq_nonneg (x i)) 2
  have hcard : 0 < (s.card : ℝ) ^ 2 := by
    positivity
  have hpow : ∑ i ∈ s, (x i ^ 2) ^ 3 = ∑ i ∈ s, x i ^ 6 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [sub_nonneg]
  rw [div_le_iff₀ hcard]
  rw [hpow] at hJensen
  simpa only [mul_comm] using hJensen

/-- Jensen on the complement of one selected coordinate, with the ambient
cardinality in the denominator. -/
theorem sixthMoment_tail_lower {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (j : ι) :
    (∑ i ∈ s.erase j, x i ^ 2) ^ 3 ≤
      (s.card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 := by
  have hJensen := pow_sum_le_card_mul_sum_pow
    (s := s.erase j) (f := fun i => x i ^ 2)
      (fun i hi => sq_nonneg (x i)) 2
  have hcard : ((s.erase j).card : ℝ) ^ 2 ≤ (s.card : ℝ) ^ 2 := by
    have hbase : ((s.erase j).card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast (Finset.card_erase_le (s := s) (a := j))
    exact pow_le_pow_left₀ (by positivity) hbase 2
  have hsum : 0 ≤ ∑ i ∈ s.erase j, x i ^ 6 := by positivity
  calc
    (∑ i ∈ s.erase j, x i ^ 2) ^ 3
        ≤ ((s.erase j).card : ℝ) ^ 2 *
          ∑ i ∈ s.erase j, (x i ^ 2) ^ 3 := hJensen
    _ = ((s.erase j).card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (s.card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 :=
      mul_le_mul_of_nonneg_right hcard hsum

/-- The sixth-power form of Guth--Maynard equation (4.3).  Taking sixth and
square roots of its two branches gives the scalar inequality used in Lemma
4.2. -/
theorem coordinate_sixth_le_trace_dispersion_max {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (j : ι) (hj : j ∈ s) :
    x j ^ 6 ≤ max
      (4 * ((∑ i ∈ s, x i ^ 6) -
        (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 2))
      (8 * (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 3) := by
  let K : ℝ := s.card
  let S : ℝ := ∑ i ∈ s, x i ^ 2
  let Q : ℝ := ∑ i ∈ s, x i ^ 6
  let y : ℝ := x j ^ 2
  let B : ℝ := ∑ i ∈ s.erase j, x i ^ 2
  let R : ℝ := ∑ i ∈ s.erase j, x i ^ 6
  let A : ℝ := Q - S ^ 3 / K ^ 2
  have hs : s.Nonempty := ⟨j, hj⟩
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast Finset.card_pos.mpr hs
  have hKsq : 0 < K ^ 2 := by positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by
    dsimp [A, Q, S, K]
    exact sixthMoment_dispersion_nonneg s x hs
  have hsumTwo : B + y = S := by
    dsimp [B, y, S]
    exact Finset.sum_erase_add s (fun i => x i ^ 2) hj
  have hsumSix : R + x j ^ 6 = Q := by
    dsimp [R, Q]
    exact Finset.sum_erase_add s (fun i => x i ^ 6) hj
  have hyCube : y ^ 3 = x j ^ 6 := by dsimp [y]; ring
  have htail : B ^ 3 ≤ K ^ 2 * R := by
    simpa only [B, K, R] using sixthMoment_tail_lower s x j
  by_cases hAverage : y ≤ 2 * S / K
  · have hcube := pow_le_pow_left₀ hy hAverage 3
    have hbranch : x j ^ 6 ≤ 8 * S ^ 3 / K ^ 3 := by
      rw [← hyCube]
      calc
        y ^ 3 ≤ (2 * S / K) ^ 3 := hcube
        _ = 8 * S ^ 3 / K ^ 3 := by ring
    exact hbranch.trans (le_max_right _ _)
  · have hdiv : 2 * S / K < y := lt_of_not_ge hAverage
    have hmul : 2 * S < y * K := (div_lt_iff₀ hK).mp hdiv
    have hyPos : 0 < y := by
      by_contra hyNot
      have hyZero : y = 0 := le_antisymm (le_of_not_gt hyNot) hy
      rw [hyZero] at hmul
      nlinarith
    have hsquare : (2 * S) ^ 2 < (y * K) ^ 2 :=
      (sq_lt_sq₀ (by positivity) (by positivity)).2 hmul
    have hstrong : 4 * S ^ 2 * y < K ^ 2 * y ^ 3 := by
      have hmulY := mul_lt_mul_of_pos_right hsquare hyPos
      nlinarith
    have hyS : y ≤ S := by nlinarith [hB]
    have hrem : 0 ≤ y ^ 2 * (3 * S - y) := by
      exact mul_nonneg (sq_nonneg y) (by linarith)
    have hdiff : S ^ 3 - B ^ 3 ≤ 3 * S ^ 2 * y := by
      have hid : S ^ 3 - B ^ 3 = 3 * S ^ 2 * y - 3 * S * y ^ 2 + y ^ 3 := by
        rw [← hsumTwo]
        ring
      rw [hid]
      nlinarith
    have hscaled : K ^ 2 * y ^ 3 ≤ 4 * (K ^ 2 * Q - S ^ 3) := by
      nlinarith
    have hAeq : K ^ 2 * A = K ^ 2 * Q - S ^ 3 := by
      dsimp [A]
      field_simp
    have hbranchY : y ^ 3 ≤ 4 * A := by
      apply le_of_mul_le_mul_of_pos_left _ hKsq
      calc
        K ^ 2 * y ^ 3 ≤ 4 * (K ^ 2 * Q - S ^ 3) := hscaled
        _ = K ^ 2 * (4 * A) := by rw [← hAeq]; ring
    have hbranch : x j ^ 6 ≤ 4 * A := by simpa only [hyCube] using hbranchY
    exact hbranch.trans (le_max_left _ _)

/-- Removing the sixth power in the dispersion branch.  The numerical
factor is written in the source-faithful form `2`. -/
theorem sixthRoot_dispersion_bound {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A)
    (h : x ^ 6 ≤ 4 * A) :
    x ≤ 2 * A ^ ((6 : ℝ)⁻¹) := by
  have h64 : x ^ 6 ≤ 64 * A := by nlinarith
  have hr : x ≤ (64 * A) ^ ((6 : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos hx (mul_nonneg (by norm_num) hA)
      (by norm_num : (0 : ℝ) < 6)]
    calc
      Real.rpow x (6 : ℝ) = x ^ (6 : ℕ) := Real.rpow_natCast x 6
      _ ≤ 64 * A := h64
  calc
    x ≤ (64 * A) ^ ((6 : ℝ)⁻¹) := hr
    _ = 64 ^ ((6 : ℝ)⁻¹) * A ^ ((6 : ℝ)⁻¹) := by
      rw [Real.mul_rpow (by norm_num) hA]
    _ = 2 * A ^ ((6 : ℝ)⁻¹) := by norm_num

/-- Removing the sixth power in the average-square branch. -/
theorem sixthRoot_cubic_bound {x B : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B)
    (h : x ^ 6 ≤ 8 * B ^ 3) :
    x ≤ 2 * B ^ ((2 : ℝ)⁻¹) := by
  have hB3 : 0 ≤ B ^ 3 := pow_nonneg hB 3
  have h64 : x ^ 6 ≤ 64 * B ^ 3 := by nlinarith
  have hr : x ≤ (64 * B ^ 3) ^ ((6 : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos hx (mul_nonneg (by norm_num) hB3)
      (by norm_num : (0 : ℝ) < 6)]
    calc
      Real.rpow x (6 : ℝ) = x ^ (6 : ℕ) := Real.rpow_natCast x 6
      _ ≤ 64 * B ^ 3 := h64
  calc
    x ≤ (64 * B ^ 3) ^ ((6 : ℝ)⁻¹) := hr
    _ = 64 ^ ((6 : ℝ)⁻¹) * (B ^ 3) ^ ((6 : ℝ)⁻¹) := by
      rw [Real.mul_rpow (by norm_num) hB3]
    _ = 2 * B ^ ((2 : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast_mul hB 3 ((6 : ℝ)⁻¹)]
      norm_num

/-- The scalar sixth-root conclusion of Guth--Maynard Lemma 4.2. -/
theorem coordinate_le_trace_dispersion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (j : ι) (hj : j ∈ s) :
    x j ≤
      2 * ((∑ i ∈ s, x i ^ 6) -
        (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 2) ^ ((6 : ℝ)⁻¹) +
      2 * ((∑ i ∈ s, x i ^ 2) / (s.card : ℝ)) ^ ((2 : ℝ)⁻¹) := by
  let A : ℝ := (∑ i ∈ s, x i ^ 6) -
    (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 2
  let B : ℝ := (∑ i ∈ s, x i ^ 2) / (s.card : ℝ)
  have hs : s.Nonempty := ⟨j, hj⟩
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hA : 0 ≤ A := by
    exact sixthMoment_dispersion_nonneg s x hs
  have hB : 0 ≤ B := by
    exact div_nonneg (by positivity) hcard.le
  have h6 := coordinate_sixth_le_trace_dispersion_max s x j hj
  by_cases hbranches : 4 * A ≤
      8 * (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 3
  · have h6B : x j ^ 6 ≤ 8 * B ^ 3 := by
      calc
        x j ^ 6 ≤ max (4 * A)
            (8 * (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 3) := h6
        _ = 8 * (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 3 :=
          max_eq_right hbranches
        _ = 8 * B ^ 3 := by rw [show B = _ by rfl, div_pow]; ring
    have hroot := sixthRoot_cubic_bound (hx j hj) hB h6B
    have hArpow : 0 ≤ A ^ ((6 : ℝ)⁻¹) := Real.rpow_nonneg hA _
    dsimp only [A, B] at hroot ⊢
    linarith
  · have h6A : x j ^ 6 ≤ 4 * A := by
      calc
        x j ^ 6 ≤ max (4 * A)
            (8 * (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 3) := h6
        _ = 4 * A := max_eq_left (le_of_not_ge hbranches)
    have hroot := sixthRoot_dispersion_bound (hx j hj) hA h6A
    have hBrpow : 0 ≤ B ^ ((2 : ℝ)⁻¹) := Real.rpow_nonneg hB _
    dsimp only [A, B] at hroot ⊢
    linarith

/-- Sampling-matrix specialization of the sixth-power form of
Guth--Maynard Lemma 4.2.  The two sums are respectively the first and cubic
spectral moments of the positive row Gram matrix. -/
theorem gmMatrix_singularValue_sixth_le_dispersion_max
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) (j : GMRow W) :
    gmMatrixSingularValue cutoff N W j ^ 6 ≤
      max
        (4 * ((∑ i : GMRow W,
            (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3) -
          (∑ i : GMRow W,
            (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
            (W.card : ℝ) ^ 2))
        (8 * (∑ i : GMRow W,
            (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
            (W.card : ℝ) ^ 3) := by
  let s : Finset (GMRow W) := Finset.univ
  let x : GMRow W → ℝ := gmMatrixSingularValue cutoff N W
  have hj : j ∈ s := Finset.mem_univ j
  have hbound := coordinate_sixth_le_trace_dispersion_max s x j hj
  have hsquare : ∀ i : GMRow W, x i ^ 2 =
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i := by
    intro i
    exact gmMatrixSingularValue_sq cutoff N W i
  have hsixth : ∀ i : GMRow W, x i ^ 6 =
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3 := by
    intro i
    exact gmMatrixSingularValue_sixth cutoff N W i
  simpa only [s, x, Finset.sum_const_zero, Finset.filter_true_of_mem,
    Finset.sum_filter, Finset.card_univ, Fintype.card_coe,
    hsquare, hsixth] using hbound

/-- Sampling-matrix specialization of the sixth-root conclusion in
Guth--Maynard Lemma 4.2. -/
theorem gmMatrix_singularValue_le_trace_dispersion
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) (j : GMRow W) :
    gmMatrixSingularValue cutoff N W j ≤
      2 * ((∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3) -
        (∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
          (W.card : ℝ) ^ 2) ^ ((6 : ℝ)⁻¹) +
      2 * ((∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) /
          (W.card : ℝ)) ^ ((2 : ℝ)⁻¹) := by
  let s : Finset (GMRow W) := Finset.univ
  let x : GMRow W → ℝ := gmMatrixSingularValue cutoff N W
  have hx : ∀ i ∈ s, 0 ≤ x i := by
    intro i hi
    exact gmMatrixSingularValue_nonneg cutoff N W i
  have hbound := coordinate_le_trace_dispersion s x hx j (Finset.mem_univ j)
  have hsquare : ∀ i : GMRow W, x i ^ 2 =
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i := by
    intro i
    exact gmMatrixSingularValue_sq cutoff N W i
  have hsixth : ∀ i : GMRow W, x i ^ 6 =
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3 := by
    intro i
    exact gmMatrixSingularValue_sixth cutoff N W i
  simpa only [s, x, Finset.card_univ, Fintype.card_coe,
    hsquare, hsixth] using hbound

/-- Exact operator-norm conclusion of Guth--Maynard Lemma 4.2 for the
sampling matrix. -/
theorem gmMatrix_operatorNorm_le_trace_dispersion
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) (hW : W.Nonempty) :
    gmMatrixOperatorNorm cutoff N W ≤
      2 * ((∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3) -
        (∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
          (W.card : ℝ) ^ 2) ^ ((6 : ℝ)⁻¹) +
      2 * ((∑ i : GMRow W,
          (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) /
          (W.card : ℝ)) ^ ((2 : ℝ)⁻¹) := by
  obtain ⟨j, hj⟩ := exists_gmMatrixOperatorNorm_le_singularValue cutoff N W hW
  exact hj.trans (gmMatrix_singularValue_le_trace_dispersion cutoff N W j)

end RiemannZeta.GuthMaynard

import GuthMaynard.ClassicalLargeValues
import GuthMaynard.HeathBrownReflection

/-!
# Jutila's amplified finite Gram entry

This is the source-entry step preceding reflection in Jutila (1977),
equation (1.4); compare Ivić, §9.5, equations (9.38)--(9.41).
The kernel is the actual cutoff-squared trace polynomial. No reflection,
moment estimate, or large-values exponent is assumed or claimed here.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Phase-aligned duality for an arbitrary finite sampling family. -/
theorem finite_sampling_gram {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (a : ι → ℂ) (y : κ → ι → ℂ)
    {V : ℝ} (hV : 0 ≤ V)
    (hlarge : ∀ t ∈ W, V ≤ ‖∑ n ∈ s, a n * y t n‖) :
    ((W.card : ℝ) * V) ^ 2 ≤
      (∑ n ∈ s, ‖a n‖ ^ 2) *
        ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (y t n) * y u n‖ := by
  let D := fun t => ∑ n ∈ s, a n * y t n
  let c := fun t => phaseAlign (D t)
  have halign : ‖∑ t ∈ W, c t * D t‖ = ∑ t ∈ W, ‖D t‖ := by
    have heq : (∑ t ∈ W, c t * D t) = ((∑ t ∈ W, ‖D t‖ : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl (fun t _ => phaseAlign_mul (D t))
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hlow : (W.card : ℝ) * V ≤ ∑ t ∈ W, ‖D t‖ := by
    calc
      _ = ∑ _t ∈ W, V := by simp
      _ ≤ _ := Finset.sum_le_sum hlarge
  have hexpand : (∑ t ∈ W, c t * D t) =
      ∑ n ∈ s, a n * (∑ t ∈ W, c t * y t n) := by
    simp only [D, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hcs := norm_sum_mul_sq_le s a (fun n => ∑ t ∈ W, c t * y t n)
  rw [← hexpand] at hcs
  have hg := sum_norm_sq_sum_le_gram s W c y
    (fun t _ => norm_phaseAlign_le_one (D t))
  calc
    _ ≤ ‖∑ t ∈ W, c t * D t‖ ^ 2 := by
      rw [halign]
      exact pow_le_pow_left₀ (mul_nonneg (by positivity) hV) hlow 2
    _ ≤ _ := hcs.trans (mul_le_mul_of_nonneg_left hg (by positivity))

/-- The actual smoothed sampling Gram kernel is the trace polynomial. -/
theorem jutila_smooth_gram_kernel (cutoff : GMSmoothCutoff) (N : ℕ) (t u : ℝ) :
    (∑ n ∈ dyadicInterval N,
      conj ((cutoff ((n : ℝ) / N) : ℂ) * (n : ℂ) ^ ((t : ℂ) * I)) *
        ((cutoff ((n : ℝ) / N) : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))) =
      heathBrownTracePolynomial cutoff N (u - t) := by
  rw [heathBrownTracePolynomial_eq_source]
  unfold sourceDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hphase := heathBrownPhase_mul_star n hnpos (-u) (-t)
  have hid (x : ℝ) :
      heathBrownPhase n (-x) = (n : ℂ) ^ ((x : ℂ) * I) := by
    simp [heathBrownPhase]
  have hdiff : -u - -t = -(u-t) := by ring
  rw [hdiff, hid, hid, hid] at hphase
  simp only [map_mul, Complex.conj_ofReal]
  rw [← hphase, Complex.star_def]
  push_cast
  ring

/-- Smoothed Halász--Montgomery duality with unit-bounded coefficients. -/
theorem jutila_smooth_duality (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (a : ℕ → ℂ) {V : ℝ} (hV : 0 ≤ V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N a t‖) :
    ((W.card : ℝ) * V) ^ 2 ≤ (N : ℝ) *
      ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownTracePolynomial cutoff N (u-t)‖ := by
  have hentry (t : ℝ) :
      (∑ n ∈ dyadicInterval N, a n *
        ((cutoff ((n : ℝ) / N) : ℂ) * (n : ℂ) ^ ((t : ℂ) * I))) =
      gmSmoothDirichletPoly cutoff N a t := by
    unfold gmSmoothDirichletPoly
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have h := finite_sampling_gram (dyadicInterval N) W a
    (fun t n => (cutoff ((n : ℝ) / N) : ℂ) * (n : ℂ) ^ ((t : ℂ) * I)) hV
    (fun t ht => by rw [hentry]; exact hlarge t ht)
  simp_rw [jutila_smooth_gram_kernel] at h
  have hc : ∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ dyadicInterval N, (1 : ℝ) :=
        Finset.sum_le_sum (fun n hn => by
          simpa using pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2)
      _ = _ := by simp [dyadicInterval]; omega
  exact h.trans (mul_le_mul_of_nonneg_right hc (by positivity))

/-- The full off-diagonal moment; the diagonal is literally removed. -/
def jutilaOffDiagonalMoment (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖ ^ (2*k)

theorem jutilaOffDiagonalMoment_nonneg (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (k : ℕ) : 0 ≤ jutilaOffDiagonalMoment cutoff N W k := by
  unfold jutilaOffDiagonalMoment
  positivity

/-- Hölder on all ordered pairs, with zero on the diagonal. -/
theorem jutila_off_diagonal_holder (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) {k : ℕ} (hk : 0 < k) :
    (∑ t ∈ W, ∑ u ∈ W,
      if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖) ^ (2*k) ≤
      (W.card : ℝ) ^ (4*k-2) * jutilaOffDiagonalMoment cutoff N W k := by
  classical
  let f : ℝ × ℝ → ℝ := fun p =>
    if p.1 = p.2 then 0 else ‖heathBrownTracePolynomial cutoff N (p.2-p.1)‖
  have h := pow_sum_le_card_mul_sum_pow (s := W.product W) (f := f)
    (by intro p hp; dsimp [f]; positivity) (2*k-1)
  have hk' : 2*k-1+1 = 2*k := by omega
  rw [hk'] at h
  rw [Finset.product_eq_sprod] at h
  simp_rw [Finset.sum_product] at h
  rw [Finset.card_product] at h
  simp only [Nat.cast_mul, f] at h
  have hc : ((W.card : ℝ) * W.card) ^ (2*k-1) = (W.card : ℝ) ^ (4*k-2) := by
    rw [← sq, ← pow_mul]
    congr 1
    omega
  rw [hc] at h
  convert h using 1
  unfold jutilaOffDiagonalMoment
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp [show 2*k ≠ 0 by omega]

/-- Separate the actual Gram diagonal before applying a higher moment. -/
theorem jutila_smooth_duality_off_diagonal (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (a : ℕ → ℂ) {V : ℝ} (hV : 0 ≤ V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N a t‖) :
    ((W.card : ℝ) * V) ^ 2 ≤ (W.card : ℝ) * N ^ 2 + (N : ℝ) *
      ∑ t ∈ W, ∑ u ∈ W,
        if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖ := by
  have hd := jutila_smooth_duality cutoff N W a hV ha hlarge
  have hsplit : (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownTracePolynomial cutoff N (u-t)‖) ≤
      (W.card : ℝ) * N +
        ∑ t ∈ W, ∑ u ∈ W,
          if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖ := by
    classical
    have hrow (t : ℝ) (ht : t ∈ W) :
        (∑ u ∈ W, ‖heathBrownTracePolynomial cutoff N (u-t)‖) ≤ (N : ℝ) +
          ∑ u ∈ W, if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖ := by
      calc
        _ = ‖heathBrownTracePolynomial cutoff N (t-t)‖ +
            ∑ u ∈ W, if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖ := by
          have hpoint (u : ℝ) : ‖heathBrownTracePolynomial cutoff N (u-t)‖ =
              (if t = u then ‖heathBrownTracePolynomial cutoff N (t-t)‖ else 0) +
                (if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖) := by
            split_ifs with h <;> simp_all
          have heq := Finset.sum_congr rfl (fun u (_ : u ∈ W) => hpoint u)
          simpa [Finset.sum_add_distrib, ht] using heq
        _ ≤ _ := add_le_add_left (norm_heathBrownTracePolynomial_le cutoff N _) _
    calc
      _ ≤ ∑ t ∈ W, ((N : ℝ) +
          ∑ u ∈ W, if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖) :=
        Finset.sum_le_sum hrow
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have h := hd.trans (mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg N))
  nlinarith

/-- Either the diagonal already proves the sharp cardinality scale, or
the actual off-diagonal trace has the required amplified mass. -/
theorem jutila_smooth_amplified_gram (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (a : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N a t‖)
    {k : ℕ} (hk : 0 < k) :
    (W.card : ℝ) * V ^ 2 ≤ 2 * (N : ℝ) ^ 2 ∨
      (W.card : ℝ) ^ 2 * V ^ (4*k) ≤
        (2 * (N : ℝ)) ^ (2*k) * jutilaOffDiagonalMoment cutoff N W k := by
  classical
  by_cases hsmall : (W.card : ℝ) * V ^ 2 ≤ 2 * (N : ℝ) ^ 2
  · exact Or.inl hsmall
  right
  have hbig := lt_of_not_ge hsmall
  have hR : 0 < (W.card : ℝ) := by
    by_contra h
    have hzero : (W.card : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hzero] at hbig
    nlinarith [sq_nonneg (N : ℝ)]
  let S := ∑ t ∈ W, ∑ u ∈ W,
    if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖
  have hdual := jutila_smooth_duality_off_diagonal cutoff N W a hV.le ha hlarge
  change ((W.card : ℝ) * V) ^ 2 ≤ (W.card : ℝ) * N ^ 2 + (N : ℝ) * S at hdual
  have hmain : (W.card : ℝ) ^ 2 * V ^ 2 ≤ 2 * (N : ℝ) * S := by
    nlinarith [mul_pos hR (sub_pos.mpr hbig)]
  have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ (W.card : ℝ) ^ 2 * V ^ 2)
    hmain (2*k)
  have hholder := jutila_off_diagonal_holder cutoff N W hk
  change S ^ (2*k) ≤ (W.card : ℝ) ^ (4*k-2) * jutilaOffDiagonalMoment cutoff N W k at hholder
  have hcombine : ((W.card : ℝ) ^ 2 * V ^ 2) ^ (2*k) ≤
      (2 * (N : ℝ)) ^ (2*k) *
        ((W.card : ℝ) ^ (4*k-2) * jutilaOffDiagonalMoment cutoff N W k) := by
    calc
      _ ≤ (2 * (N : ℝ) * S) ^ (2*k) := hpower
      _ = (2 * (N : ℝ)) ^ (2*k) * S ^ (2*k) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hholder (by positivity)
  have hleft : ((W.card : ℝ) ^ 2 * V ^ 2) ^ (2*k) =
      (W.card : ℝ) ^ (4*k-2) * ((W.card : ℝ) ^ 2 * V ^ (4*k)) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    have heq : 2*(2*k) = 4*k := by omega
    rw [heq, ← mul_assoc, ← pow_add]
    congr 1
    congr 1
    omega
  rw [hleft] at hcombine
  have hfactor : (W.card : ℝ) ^ (4*k-2) *
      ((W.card : ℝ) ^ 2 * V ^ (4*k)) ≤
      (W.card : ℝ) ^ (4*k-2) *
        ((2 * (N : ℝ)) ^ (2*k) * jutilaOffDiagonalMoment cutoff N W k) := by
    convert hcombine using 1; ring
  exact (mul_le_mul_iff_right₀ (pow_pos hR _)).mp hfactor

end TaoTrudgianYang2025

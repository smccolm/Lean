import RiemannZeta.GuthMaynard.HughesYoungHighTail

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Exact product truncation of the Hughes--Young opening
-/

noncomputable def hughesYoungHighPairProductLow
    (q : ℕ) (t u R : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if (p.1 : ℝ) * p.2 ≤ R then
      hughesYoungRightPairTerm t (2 * q) u p
    else 0

theorem summable_hughesYoungHighPairProductLow
    {q : ℕ} (hq : 0 < q) (t u R : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      if (p.1 : ℝ) * p.2 ≤ R then
        hughesYoungRightPairTerm t (2 * q) u p
      else 0) := by
  have hfull : Summable (hughesYoungRightPairTerm t (2 * q) u) :=
    summable_hughesYoungRightPairTerm t u (by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith)
  simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
    Summable.indicator hfull {p | (p.1 : ℝ) * p.2 ≤ R}

theorem summable_hughesYoungHighPairProductTail
    {q : ℕ} (hq : 0 < q) (t u R : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      if R < (p.1 : ℝ) * p.2 then
        hughesYoungRightPairTerm t (2 * q) u p
      else 0) := by
  have hfull : Summable (hughesYoungRightPairTerm t (2 * q) u) :=
    summable_hughesYoungRightPairTerm t u (by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith)
  simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
    Summable.indicator hfull {p | R < (p.1 : ℝ) * p.2}

theorem tsum_hughesYoungRightPairTerm_eq_productLow_add_tail
    {q : ℕ} (hq : 0 < q) (t u R : ℝ) :
    (∑' p : ℕ × ℕ, hughesYoungRightPairTerm t (2 * q) u p) =
      hughesYoungHighPairProductLow q t u R +
        hughesYoungHighPairProductTail q t u R := by
  have hlow := summable_hughesYoungHighPairProductLow hq t u R
  have htail := summable_hughesYoungHighPairProductTail hq t u R
  unfold hughesYoungHighPairProductLow hughesYoungHighPairProductTail
  rw [← hlow.tsum_add htail]
  apply tsum_congr
  intro p
  by_cases hp : (p.1 : ℝ) * p.2 ≤ R
  · simp [hp, not_lt.mpr hp]
  · have hp' : R < (p.1 : ℝ) * p.2 := lt_of_not_ge hp
    simp [hp, hp']

noncomputable def hughesYoungIntegratedProductLow
    (q : ℕ) (t H R : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if (p.1 : ℝ) * p.2 ≤ R then
      ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p
    else 0

noncomputable def hughesYoungIntegratedProductTail
    (q : ℕ) (t H R : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if R < (p.1 : ℝ) * p.2 then
      ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p
    else 0

noncomputable def hughesYoungHighTailContinuousMap
    (q : ℕ) (t R : ℝ) (hc : (1 / 2 : ℝ) < 2 * q)
    (p : ℕ × ℕ) : C(ℝ, ℂ) :=
  if R < (p.1 : ℝ) * p.2 then
    hughesYoungRightPairContinuousMap t (2 * q) hc p
  else 0

theorem summable_hughesYoungHighTailContinuousMap_restrict_norm
    {q : ℕ} (hq : 0 < q) (t H R : ℝ) :
    let hc : (1 / 2 : ℝ) < 2 * q := by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    Summable (fun p : ℕ × ℕ =>
      ‖(hughesYoungHighTailContinuousMap q t R hc p).restrict
        (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
  let hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfull := summable_hughesYoungRightPair_restrict_norm t H hc
  have hind := Summable.indicator hfull
    {p : ℕ × ℕ | R < (p.1 : ℝ) * p.2}
  apply hind.congr
  intro p
  by_cases hp : R < (p.1 : ℝ) * p.2
  · simp [hughesYoungHighTailContinuousMap, hp]
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_neg hp,
      hughesYoungHighTailContinuousMap]
    change 0 = ‖(0 : C(↑(⟨Set.uIcc (-H) H, isCompact_uIcc⟩ :
      TopologicalSpace.Compacts ℝ), ℂ))‖
    simp

theorem hughesYoungIntegratedProductTail_eq_intervalIntegral
    {q : ℕ} (hq : 0 < q) (t H R : ℝ) :
    hughesYoungIntegratedProductTail q t H R =
      ∫ u in -H..H, hughesYoungHighPairProductTail q t u R := by
  let hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hsum := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_hughesYoungHighTailContinuousMap_restrict_norm hq t H R)
  calc
    hughesYoungIntegratedProductTail q t H R =
        ∑' p : ℕ × ℕ,
          ∫ u in -H..H, hughesYoungHighTailContinuousMap q t R hc p u := by
      unfold hughesYoungIntegratedProductTail
      apply tsum_congr
      intro p
      by_cases hp : R < (p.1 : ℝ) * p.2
      · simp [hughesYoungHighTailContinuousMap, hp,
          hughesYoungRightPairContinuousMap]
      · simp [hughesYoungHighTailContinuousMap, hp]
    _ = ∫ u in -H..H,
        ∑' p : ℕ × ℕ, hughesYoungHighTailContinuousMap q t R hc p u := hsum
    _ = ∫ u in -H..H, hughesYoungHighPairProductTail q t u R := by
      apply intervalIntegral.integral_congr
      intro u _hu
      unfold hughesYoungHighPairProductTail
      apply tsum_congr
      intro p
      by_cases hp : R < (p.1 : ℝ) * p.2
      · simp [hughesYoungHighTailContinuousMap, hp,
          hughesYoungRightPairContinuousMap]
      · simp [hughesYoungHighTailContinuousMap, hp]

theorem exists_norm_hughesYoungIntegratedProductTail_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T t R H : ℝ},
      1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 < R → 0 ≤ H →
      ‖hughesYoungIntegratedProductTail q t H R‖ ≤
        (256 * Real.exp (400 * (q : ℝ) ^ 2) *
          ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          R ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η) * L := by
  obtain ⟨L, hL, hbound⟩ :=
    exists_intervalIntegral_hughesYoungHighPairProductTail_le
      q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro T t R H hT ht hR hH
  rw [hughesYoungIntegratedProductTail_eq_intervalIntegral hq]
  exact hbound hT ht hR hH

/-- The full finite-height zeta product is exactly the low-product opening
plus the high-line tail; no infinite arithmetic term is dropped. -/
theorem hughesYoungFiniteZetaProduct_even_eq_productLow_add_tail
    {q : ℕ} (hq : 0 < q) (t H R : ℝ) :
    hughesYoungFiniteZetaProduct t (2 * q) H =
      (1 / (Real.pi : ℂ)) *
        (hughesYoungIntegratedProductLow q t H R +
          hughesYoungIntegratedProductTail q t H R) := by
  unfold hughesYoungFiniteZetaProduct
  have hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfull : Summable (fun p : ℕ × ℕ =>
      ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) :=
    (intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (summable_hughesYoungRightPair_restrict_norm t H hc)).summable
  have hlow : Summable (fun p : ℕ × ℕ =>
      if (p.1 : ℝ) * p.2 ≤ R then
        ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p
      else 0) := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
      Summable.indicator hfull {p | (p.1 : ℝ) * p.2 ≤ R}
  have htail : Summable (fun p : ℕ × ℕ =>
      if R < (p.1 : ℝ) * p.2 then
        ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p
      else 0) := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
      Summable.indicator hfull {p | R < (p.1 : ℝ) * p.2}
  unfold hughesYoungIntegratedProductLow hughesYoungIntegratedProductTail
  congr 1
  rw [← hlow.tsum_add htail]
  apply tsum_congr
  intro p
  by_cases hp : (p.1 : ℝ) * p.2 ≤ R
  · simp [hp, not_lt.mpr hp]
  · have hp' : R < (p.1 : ℝ) * p.2 := lt_of_not_ge hp
    simp [hp, hp']

theorem norm_hughesYoungFiniteZetaProduct_even_sub_productLow_le
    {q : ℕ} (hq : 0 < q) (t H R : ℝ) :
    ‖hughesYoungFiniteZetaProduct t (2 * q) H -
        (1 / (Real.pi : ℂ)) *
          hughesYoungIntegratedProductLow q t H R‖ ≤
      ‖hughesYoungIntegratedProductTail q t H R‖ := by
  rw [hughesYoungFiniteZetaProduct_even_eq_productLow_add_tail hq]
  have hpi : 1 / ‖(Real.pi : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  calc
    ‖(1 / (Real.pi : ℂ)) *
          (hughesYoungIntegratedProductLow q t H R +
            hughesYoungIntegratedProductTail q t H R) -
        (1 / (Real.pi : ℂ)) *
          hughesYoungIntegratedProductLow q t H R‖ =
      ‖(1 / (Real.pi : ℂ)) *
        hughesYoungIntegratedProductTail q t H R‖ := by
      congr 1
      ring
    _ = (1 / ‖(Real.pi : ℂ)‖) *
        ‖hughesYoungIntegratedProductTail q t H R‖ := by
      rw [norm_mul, norm_div, norm_one]
    _ ≤ _ := by
      exact mul_le_of_le_one_left (norm_nonneg _) hpi

end RiemannZeta.GuthMaynard

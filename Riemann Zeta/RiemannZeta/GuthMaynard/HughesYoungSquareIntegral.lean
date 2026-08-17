import RiemannZeta.GuthMaynard.HughesYoungSquareTruncation

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Integrated square truncation

This is the exact finite rectangular opening needed by the Hughes--Young
four-index moment.  The discarded pair family is retained as an explicit
integrated tail and bounded on every finite Mellin segment.
-/

noncomputable def hughesYoungIntegratedHighPairSquare
    (q : ℕ) (t H : ℝ) (M : ℕ) : ℂ :=
  ∑ p ∈ Finset.Icc (1, 1) (M, M),
    ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p

noncomputable def hughesYoungIntegratedHighPairSquareTail
    (q : ℕ) (t H : ℝ) (M : ℕ) : ℂ :=
  ∫ u in -H..H, hughesYoungHighPairSquareTail q t u M

noncomputable def hughesYoungHighPairSquareTailContinuousMap
    (q : ℕ) (t : ℝ) (M : ℕ) (hc : (1 / 2 : ℝ) < 2 * q)
    (p : ℕ × ℕ) : C(ℝ, ℂ) :=
  if M < p.1 ∨ M < p.2 then
    hughesYoungRightPairContinuousMap t (2 * q) hc p
  else 0

theorem summable_hughesYoungHighPairSquareTailContinuousMap_restrict_norm
    {q : ℕ} (hq : 0 < q) (t H : ℝ) (M : ℕ) :
    let hc : (1 / 2 : ℝ) < 2 * q := by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    Summable (fun p : ℕ × ℕ =>
      ‖(hughesYoungHighPairSquareTailContinuousMap q t M hc p).restrict
        (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
  let hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfull := summable_hughesYoungRightPair_restrict_norm t H hc
  have hind := Summable.indicator hfull
    {p : ℕ × ℕ | M < p.1 ∨ M < p.2}
  apply hind.congr
  intro p
  by_cases hp : M < p.1 ∨ M < p.2
  · simp [hughesYoungHighPairSquareTailContinuousMap, hp]
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_neg hp,
      hughesYoungHighPairSquareTailContinuousMap]
    change 0 = ‖(0 : C(↑(⟨Set.uIcc (-H) H, isCompact_uIcc⟩ :
      TopologicalSpace.Compacts ℝ), ℂ))‖
    simp

theorem tsum_intervalIntegral_hughesYoungHighPairSquareTail
    {q : ℕ} (hq : 0 < q) (t H : ℝ) (M : ℕ) :
    ∑' p : ℕ × ℕ,
        ∫ u in -H..H, (
          if M < p.1 ∨ M < p.2 then
            hughesYoungRightPairTerm t (2 * q) u p else 0) =
      hughesYoungIntegratedHighPairSquareTail q t H M := by
  let hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hsum := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_hughesYoungHighPairSquareTailContinuousMap_restrict_norm
      hq t H M)
  rw [hughesYoungIntegratedHighPairSquareTail]
  calc
    (∑' p : ℕ × ℕ,
        ∫ u in -H..H, (
          if M < p.1 ∨ M < p.2 then
            hughesYoungRightPairTerm t (2 * q) u p else 0)) =
      ∑' p : ℕ × ℕ,
        ∫ u in -H..H,
          hughesYoungHighPairSquareTailContinuousMap q t M hc p u := by
        apply tsum_congr
        intro p
        by_cases hp : M < p.1 ∨ M < p.2
        · simp [hughesYoungHighPairSquareTailContinuousMap, hp,
            hughesYoungRightPairContinuousMap]
        · simp [hughesYoungHighPairSquareTailContinuousMap, hp]
    _ = ∫ u in -H..H,
        ∑' p : ℕ × ℕ,
          hughesYoungHighPairSquareTailContinuousMap q t M hc p u := hsum
    _ = ∫ u in -H..H, hughesYoungHighPairSquareTail q t u M := by
      apply intervalIntegral.integral_congr
      intro u _hu
      unfold hughesYoungHighPairSquareTail
      apply tsum_congr
      intro p
      by_cases hp : M < p.1 ∨ M < p.2
      · simp [hughesYoungHighPairSquareTailContinuousMap, hp,
          hughesYoungRightPairContinuousMap]
      · simp [hughesYoungHighPairSquareTailContinuousMap, hp]

theorem hughesYoungFiniteZetaProduct_even_eq_square_add_tail
    {q : ℕ} (hq : 0 < q) (t H : ℝ) (M : ℕ) :
    hughesYoungFiniteZetaProduct t (2 * q) H =
      (1 / (Real.pi : ℂ)) *
        (hughesYoungIntegratedHighPairSquare q t H M +
          hughesYoungIntegratedHighPairSquareTail q t H M) := by
  classical
  have hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfull : Summable (fun p : ℕ × ℕ =>
      ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) :=
    (intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (summable_hughesYoungRightPair_restrict_norm t H hc)).summable
  let S : Finset (ℕ × ℕ) := Finset.Icc (1, 1) (M, M)
  have hlow : Summable (fun p : ℕ × ℕ =>
      if p ∈ S then
        (∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) else 0) := by
    apply summable_of_ne_finset_zero (s := S)
    intro p hp
    simp [hp]
  have htail : Summable (fun p : ℕ × ℕ =>
      if M < p.1 ∨ M < p.2 then
        (∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) else 0) := by
    refine (Summable.indicator hfull
      {p : ℕ × ℕ | M < p.1 ∨ M < p.2}).congr ?_
    intro p
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have htailEq :
      (∑' p : ℕ × ℕ,
        ∫ u in -H..H, (if M < p.1 ∨ M < p.2 then
          hughesYoungRightPairTerm t (2 * q) u p else 0)) =
      ∑' p : ℕ × ℕ,
        if M < p.1 ∨ M < p.2 then
          (∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) else 0 := by
    apply tsum_congr
    intro p
    by_cases hp : M < p.1 ∨ M < p.2 <;> simp [hp]
  unfold hughesYoungFiniteZetaProduct
  congr 1
  rw [show hughesYoungIntegratedHighPairSquare q t H M =
      ∑' p : ℕ × ℕ,
        if p ∈ S then
          (∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) else 0 by
    unfold hughesYoungIntegratedHighPairSquare S
    symm
    calc
      (∑' p : ℕ × ℕ,
          if p ∈ Finset.Icc (1, 1) (M, M) then
            (∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) else 0) =
        ∑ p ∈ Finset.Icc (1, 1) (M, M),
          (if p ∈ Finset.Icc (1, 1) (M, M) then
            (∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) else 0) := by
          apply tsum_eq_sum
          intro p hp
          simp [hp]
      _ = ∑ p ∈ Finset.Icc (1, 1) (M, M),
          ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [hp]
    ]
  rw [← tsum_intervalIntegral_hughesYoungHighPairSquareTail hq]
  rw [htailEq]
  rw [← hlow.tsum_add htail]
  apply tsum_congr
  intro p
  rcases p with ⟨m, n⟩
  by_cases hm0 : m = 0
  · simp [S, hm0, hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero]
  by_cases hn0 : n = 0
  · simp [S, hn0, hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero]
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  by_cases hm : m ≤ M
  · by_cases hn : n ≤ M
    · simp [S, hm1, hn1, hm, hn]
    · have hn' : M < n := Nat.lt_of_not_ge hn
      simp [S, hm1, hn1, hm, hn, hn']
  · have hm' : M < m := Nat.lt_of_not_ge hm
    simp [S, hm1, hn1, hm, hm']

theorem exists_norm_hughesYoungIntegratedHighPairSquareTail_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T t H : ℝ} {M : ℕ},
      1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 < M → 0 ≤ H →
      ‖hughesYoungIntegratedHighPairSquareTail q t H M‖ ≤
        (256 * Real.exp (400 * (q : ℝ) ^ 2) *
          ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η) * L := by
  obtain ⟨L, hL, hmoment⟩ :=
    exists_intervalIntegral_exp_neg_84_mul_one_add_abs_pow_le (4 * q + 8)
  refine ⟨L, hL, ?_⟩
  intro T t H M hT ht hM hH
  let C : ℝ := 256 * Real.exp (400 * (q : ℝ) ^ 2) *
    ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
    (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
    hughesYoungReferenceDivisorPairMass η
  let g : ℝ → ℝ := fun u =>
    Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (4 * q + 8)
  have hC0 : 0 ≤ C := by
    unfold C
    exact mul_nonneg (by positivity)
      (hughesYoungReferenceDivisorPairMass_nonneg η)
  have hg : IntervalIntegrable g volume (-H) H :=
    (integrable_exp_neg_84_mul_one_add_abs_pow (4 * q + 8)).intervalIntegrable
  have horder : -H ≤ H := by linarith
  unfold hughesYoungIntegratedHighPairSquareTail
  calc
    ‖∫ u in -H..H, hughesYoungHighPairSquareTail q t u M‖ ≤
        ∫ u in -H..H, C * g u := by
      apply intervalIntegral.norm_integral_le_of_norm_le horder
      · filter_upwards with u hu
        have hweight :=
          norm_hughesYoungRightContourWeight_even_le_on_height_support
            hT ht hq u
        have htail := norm_hughesYoungHighPairSquareTail_le
          hq hM t u hη0 hη
        have hexp :
            Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) =
              Real.exp (400 * (q : ℝ) ^ 2) *
                Real.exp (-84 * u ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hbasepow :
            ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) =
              ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
                (1 + |u|) ^ (4 * q + 8) := by
          rw [mul_pow]
        calc
          ‖hughesYoungHighPairSquareTail q t u M‖ ≤
              ‖hughesYoungRightContourWeight t (2 * q) u‖ *
                (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
                hughesYoungReferenceDivisorPairMass η := htail
          _ ≤ (256 * Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
                ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8)) *
                (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
                hughesYoungReferenceDivisorPairMass η := by
              gcongr
              exact hughesYoungReferenceDivisorPairMass_nonneg η
          _ = C * g u := by
              rw [hexp, hbasepow]
              unfold C g
              ring
      · exact hg.const_mul C
    _ = C * (∫ u in -H..H, g u) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ C * L := mul_le_mul_of_nonneg_left (hmoment hH) hC0
    _ = _ := by rfl

end RiemannZeta.GuthMaynard

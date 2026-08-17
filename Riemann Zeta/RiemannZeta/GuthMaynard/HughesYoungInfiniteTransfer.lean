import RiemannZeta.GuthMaynard.HughesYoungSquareIntegral

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Passage from the high opening line to a finite square on the small line

The high-line square truncation has an absolutely integrable complementary
tail.  This permits passage to the whole vertical line before the finite
square is shifted term by term.  Keeping the square finite at the contour
shift is the key point: no countable interchange is hidden in this step.
-/

theorem integrable_hughesYoungHighPairSquareTail
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {M : ℕ} (hM : 0 < M) :
    Integrable (fun u : ℝ => hughesYoungHighPairSquareTail q t u M) := by
  let C : ℝ := 256 * Real.exp (400 * (q : ℝ) ^ 2) *
    ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
    (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
    hughesYoungReferenceDivisorPairMass η
  let g : ℝ → ℝ := fun u =>
    Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (4 * q + 8)
  have hg : Integrable g :=
    integrable_exp_neg_84_mul_one_add_abs_pow (4 * q + 8)
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => hughesYoungHighPairSquareTail q t u M) := by
    have hc : (1 / 2 : ℝ) < 2 * q := by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have hpmeas : ∀ p : ℕ × ℕ, AEMeasurable (fun u : ℝ =>
        if M < p.1 ∨ M < p.2 then
          hughesYoungRightPairTerm t (2 * q) u p else 0) := by
      intro p
      by_cases hp : M < p.1 ∨ M < p.2
      · simpa only [hp, if_true, hughesYoungRightPairContinuousMap] using
          (hughesYoungRightPairContinuousMap t (2 * q) hc p).continuous.aemeasurable
      · simpa only [hp, if_false] using
          (continuous_const : Continuous (fun _u : ℝ => (0 : ℂ))).aemeasurable
    unfold hughesYoungHighPairSquareTail
    exact (AEMeasurable.tsum hpmeas).aestronglyMeasurable
  apply (hg.const_mul C).mono' hmeas
  filter_upwards with u
  have hweight :=
    norm_hughesYoungRightContourWeight_even_le_on_height_support hT ht hq u
  have htail := norm_hughesYoungHighPairSquareTail_le
    hq hM t u hη0 hη
  have hexp :
      Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) =
        Real.exp (400 * (q : ℝ) ^ 2) * Real.exp (-84 * u ^ 2) := by
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

noncomputable def hughesYoungWholeHighPairSquareTail
    (q : ℕ) (t : ℝ) (M : ℕ) : ℂ :=
  ∫ u : ℝ, hughesYoungHighPairSquareTail q t u M

theorem tendsto_hughesYoungIntegratedHighPairSquareTail
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {M : ℕ} (hM : 0 < M) :
    Tendsto (fun H : ℝ => hughesYoungIntegratedHighPairSquareTail q t H M)
      atTop (𝓝 (hughesYoungWholeHighPairSquareTail q t M)) := by
  unfold hughesYoungIntegratedHighPairSquareTail
    hughesYoungWholeHighPairSquareTail
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungHighPairSquareTail hq η hη0 hη hT ht hM)
    tendsto_neg_atTop_atBot tendsto_id

theorem tendsto_hughesYoungIntegratedHighPairSquare
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {M : ℕ} (hM : 0 < M) :
    Tendsto (fun H : ℝ => hughesYoungIntegratedHighPairSquare q t H M)
      atTop (𝓝 ((Real.pi : ℂ) *
          (riemannZeta (afeCriticalPoint t) ^ 2 *
            riemannZeta (afeCriticalPoint (-t)) ^ 2) -
        hughesYoungWholeHighPairSquareTail q t M)) := by
  have hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfull := tendsto_hughesYoungFiniteZetaProduct t hc
  have htail := tendsto_hughesYoungIntegratedHighPairSquareTail
    hq η hη0 hη hT ht hM
  have hscaled := hfull.const_mul (Real.pi : ℂ)
  have hdiff := hscaled.sub htail
  convert hdiff using 1
  · funext H
    rw [hughesYoungFiniteZetaProduct_even_eq_square_add_tail hq]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
    ring

noncomputable def hughesYoungIntegratedSmallPairSquare
    (T t H : ℝ) (M : ℕ) : ℂ :=
  ∑ p ∈ Finset.Icc (1, 1) (M, M),
    ∫ u in -H..H,
      hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p

theorem tendsto_hughesYoungHighSquare_sub_smallSquare_zero
    {q M : ℕ} (hq : 0 < q) {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (hSmall : 0 < hughesYoungSmallContour T) :
    Tendsto (fun H : ℝ =>
      hughesYoungIntegratedHighPairSquare q t H M -
        hughesYoungIntegratedSmallPairSquare T t H M)
      atTop (𝓝 0) := by
  classical
  unfold hughesYoungIntegratedHighPairSquare
    hughesYoungIntegratedSmallPairSquare
  have hsum : Tendsto (fun H : ℝ =>
      ∑ p ∈ Finset.Icc (1, 1) (M, M),
        ((∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) -
          ∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p))
      atTop (𝓝 (∑ _p ∈ Finset.Icc (1, 1) (M, M), (0 : ℂ))) := by
    apply tendsto_finsetSum
    intro p hp
    have hp' := Finset.mem_Icc.mp hp
    have hp₁ : 0 < p.1 :=
      Nat.zero_lt_one.trans_le (Prod.le_def.mp hp'.1).1
    have hp₂ : 0 < p.2 :=
      Nat.zero_lt_one.trans_le (Prod.le_def.mp hp'.1).2
    apply tendsto_hughesYoungRightPairTerm_vertical_sub_zero t hp₁ hp₂ hSmall
    have hsmallLe : hughesYoungSmallContour T ≤ 1 :=
      (hughesYoungSmallContour_spec hT).2.1
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  simpa only [Finset.sum_sub_distrib, Finset.sum_const_zero] using hsum

theorem tendsto_hughesYoungIntegratedSmallPairSquare
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hTexp : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {M : ℕ} (hM : 0 < M) :
    Tendsto (fun H : ℝ => hughesYoungIntegratedSmallPairSquare T t H M)
      atTop (𝓝 ((Real.pi : ℂ) *
          (riemannZeta (afeCriticalPoint t) ^ 2 *
            riemannZeta (afeCriticalPoint (-t)) ^ 2) -
        hughesYoungWholeHighPairSquareTail q t M)) := by
  have hT : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hSmall : 0 < hughesYoungSmallContour T :=
    (hughesYoungSmallContour_spec hTexp).1
  have hhigh := tendsto_hughesYoungIntegratedHighPairSquare
    hq η hη0 hη hT ht hM
  have hdiff := tendsto_hughesYoungHighSquare_sub_smallSquare_zero
    hq hTexp hSmall (t := t) (M := M)
  have hsub := hhigh.sub hdiff
  convert hsub using 1 <;> ring

end RiemannZeta.GuthMaynard

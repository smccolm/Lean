import RiemannZeta.GuthMaynard.HughesYoungSmallContourTail

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Finite-set contour transfer for the Hughes--Young opening

The contour shift is performed only after the absolutely convergent opening
has been truncated to a finite family of positive divisor pairs.  This is the
form needed for the finite dyadic family in Hughes--Young equation (69).
-/

noncomputable def hughesYoungIntegratedHighPairSet
    (q : ℕ) (t H : ℝ) (S : Finset (ℕ × ℕ)) : ℂ :=
  ∑ p ∈ S, ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p

noncomputable def hughesYoungIntegratedSmallPairSet
    (T t H : ℝ) (S : Finset (ℕ × ℕ)) : ℂ :=
  ∑ p ∈ S, ∫ u in -H..H,
    hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p

noncomputable def hughesYoungWholeSmallPairSet
    (T t : ℝ) (S : Finset (ℕ × ℕ)) : ℂ :=
  ∑ p ∈ S, ∫ u : ℝ,
    hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p

theorem tendsto_hughesYoungIntegratedHighPairSet_sub_small_zero
    {q : ℕ} (hq : 0 < q) {T t : ℝ} (hT : Real.exp 1 ≤ T)
    {S : Finset (ℕ × ℕ)}
    (hS : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2) :
    Tendsto (fun H : ℝ =>
      hughesYoungIntegratedHighPairSet q t H S -
        hughesYoungIntegratedSmallPairSet T t H S)
      atTop (𝓝 0) := by
  classical
  unfold hughesYoungIntegratedHighPairSet
    hughesYoungIntegratedSmallPairSet
  have hsum : Tendsto (fun H : ℝ =>
      ∑ p ∈ S,
        ((∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) -
          ∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p))
      atTop (𝓝 (∑ _p ∈ S, (0 : ℂ))) := by
    apply tendsto_finsetSum
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := hS p hp
    apply tendsto_hughesYoungRightPairTerm_vertical_sub_zero
      t hp₁ hp₂ (hughesYoungSmallContour_spec hT).1
    have hsmallLe : hughesYoungSmallContour T ≤ 1 :=
      (hughesYoungSmallContour_spec hT).2.1
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  simpa only [Finset.sum_sub_distrib, Finset.sum_const_zero] using hsum

theorem tendsto_hughesYoungIntegratedSmallPairSet_to_whole
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {S : Finset (ℕ × ℕ)}
    (hS : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2) :
    Tendsto (fun H : ℝ => hughesYoungIntegratedSmallPairSet T t H S)
      atTop (𝓝 (hughesYoungWholeSmallPairSet T t S)) := by
  classical
  unfold hughesYoungIntegratedSmallPairSet hughesYoungWholeSmallPairSet
  apply tendsto_finsetSum
  intro p hp
  obtain ⟨hp₁, hp₂⟩ := hS p hp
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungRightPairTerm_small hT ht hp₁ hp₂)
    tendsto_neg_atTop_atBot tendsto_id

/-- A finite positive pair family on the opening line converges to the exact
whole integral of the same family on the small line.  No countable contour
interchange is used. -/
theorem tendsto_hughesYoungIntegratedHighPairSet_to_wholeSmall
    {q : ℕ} (hq : 0 < q) {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {S : Finset (ℕ × ℕ)}
    (hS : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2) :
    Tendsto (fun H : ℝ => hughesYoungIntegratedHighPairSet q t H S)
      atTop (𝓝 (hughesYoungWholeSmallPairSet T t S)) := by
  have hsmall := tendsto_hughesYoungIntegratedSmallPairSet_to_whole
    hT ht hS
  have hdiff := tendsto_hughesYoungIntegratedHighPairSet_sub_small_zero
    hq hT (t := t) (S := S)
      hS
  have hadd := hsmall.add hdiff
  convert hadd using 1
  · funext H
    abel
  · simp

end RiemannZeta.GuthMaynard

import RiemannZeta.GuthMaynard.HughesYoungActiveComplementSourceLine

open Complex Filter MeasureTheory Topology
open scoped Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Infinite-height contour transfer for the Hughes--Young active complement

The finite signed DFI equation-(27) source is holomorphic on the source
strip.  Its two horizontal edges tend to zero, so the exact rectangle
identity identifies the limiting vertical integrals on any two positive
lines in that strip.
-/

/-- After both horizontal edges vanish, the symmetric vertical integrals
of the complete height-weighted signed active-complement source agree
asymptotically on two positive Mellin lines. -/
theorem tendsto_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_sub_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) :
    Tendsto (fun H : ℝ =>
      (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K) -
      (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K))
      atTop (nhds 0) := by
  let F : ℂ → ℂ := fun w =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementSignedSourceComplex
        T t w h k a b R K
  change Tendsto (fun H : ℝ =>
    (∫ u : ℝ in -H..H, F ((c₁ : ℂ) + (u : ℂ) * I)) -
    (∫ u : ℝ in -H..H, F ((c₀ : ℂ) + (u : ℂ) * I)))
    atTop (nhds 0)
  have htop : Tendsto (fun H : ℝ =>
      ∫ s : ℝ in c₀..c₁, F ((s : ℂ) + (H : ℂ) * I))
      atTop (nhds 0) := by
    simpa only [F] using
      tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_horizontal_atTop
        hc₀ hc hc₁ t h k ha hb R K (T := T)
  have hbottom : Tendsto (fun H : ℝ =>
      ∫ s : ℝ in c₀..c₁, F ((s : ℂ) + ((-H : ℝ) : ℂ) * I))
      atTop (nhds 0) := by
    simpa only [F] using
      tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_bottom_atTop
        hc₀ hc hc₁ t h k ha hb R K (T := T)
  have hhorizontal : Tendsto (fun H : ℝ =>
      (-I) *
        ((∫ s : ℝ in c₀..c₁, F ((s : ℂ) + (H : ℂ) * I)) -
          (∫ s : ℝ in c₀..c₁,
            F ((s : ℂ) + ((-H : ℝ) : ℂ) * I))))
      atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using (htop.sub hbottom).const_mul (-I)
  apply hhorizontal.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  have hrect :=
    heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_boundaryRect_zero
      hc₀ hc hc₁ t hH h k ha hb R K (T := T)
  change
    (∫ s : ℝ in c₀..c₁, F ((s : ℂ) + ((-H : ℝ) : ℂ) * I)) -
      (∫ s : ℝ in c₀..c₁, F ((s : ℂ) + (H : ℂ) * I)) +
      I • (∫ u : ℝ in -H..H, F ((c₁ : ℂ) + (u : ℂ) * I)) -
      I • (∫ u : ℝ in -H..H, F ((c₀ : ℂ) + (u : ℂ) * I)) = 0 at hrect
  rw [smul_eq_mul, smul_eq_mul] at hrect
  have hI :
      I * ((∫ u : ℝ in -H..H, F ((c₁ : ℂ) + (u : ℂ) * I)) -
        (∫ u : ℝ in -H..H, F ((c₀ : ℂ) + (u : ℂ) * I))) =
        (∫ s : ℝ in c₀..c₁, F ((s : ℂ) + (H : ℂ) * I)) -
        (∫ s : ℝ in c₀..c₁,
          F ((s : ℂ) + ((-H : ℝ) : ℂ) * I)) := by
    linear_combination hrect
  rw [← hI, ← mul_assoc]
  have hnegI : (-I : ℂ) * I = 1 := by
    rw [neg_mul, I_mul_I]
    simp
  rw [hnegI, one_mul]

end RiemannZeta.GuthMaynard

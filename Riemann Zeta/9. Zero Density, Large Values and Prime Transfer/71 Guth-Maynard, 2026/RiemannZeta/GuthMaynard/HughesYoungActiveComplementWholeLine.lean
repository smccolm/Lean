import RiemannZeta.GuthMaynard.HughesYoungActiveComplementTail

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Whole-line continuation of the non-lower active complement

This file continues the finite-rectangle argument on the literal
Hughes--Young/DFI source.  The opening line is the even line `Re w = 2Q`;
no contour value is supplied as a hypothesis.
-/

/-- Each exact signed-shift majorant on the even opening line is integrable.
The negative branch uses the proved `t ↦ -t`, `h ↔ k` symmetry of the
completed contour factor rather than a second analytic estimate. -/
theorem integrable_hughesYoungNonLowerActiveComplementEvenSignedMajorant
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) {Q : ℕ} (hQ : 0 < Q)
    (h k a b R : ℕ) (r : ℤ) :
    Integrable (fun u : ℝ =>
      hughesYoungNonLowerActiveComplementEvenSignedMajorant
        T t u Q h k a b R r) := by
  cases r with
  | ofNat n =>
      let C : ℝ :=
        ‖((a : ℂ) * b)⁻¹‖ * (((a * b * n ^ 2 : ℕ) : ℝ)) * (n : ℝ) *
          (‖(hughesYoungHeightWeight T t : ℂ)‖ *
            (((a * b * R : ℕ) : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2))) *
            ((n : ℝ) ^ (-2 : ℝ)) *
            (2312 * max 1
              (((1 / hughesYoungDyadicRatio) / (n : ℝ)) ^
                (-(3 / 4 : ℝ))) + 72)) *
          (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
            (hughesYoungEquation84LogBudget a b n +
              4 * Real.log (q : ℝ)) ^ 2)
      have hscale :=
        integrable_norm_hughesYoungReducedMellinScaleConstantComplex_vertical_even
          hT ht hQ h k
      have hmul := hscale.const_mul C
      rw [show (fun u : ℝ =>
          hughesYoungNonLowerActiveComplementEvenSignedMajorant
            T t u Q h k a b R (Int.ofNat n)) =
          (fun u : ℝ => C *
            ‖hughesYoungReducedMellinScaleConstantComplex T t
              (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖) by
        funext u
        simp only [hughesYoungNonLowerActiveComplementEvenSignedMajorant,
          hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor]
        dsimp only [C]
        ring]
      exact hmul
  | negSucc m =>
      let n : ℕ := m + 1
      let C : ℝ :=
        ‖((b : ℂ) * a)⁻¹‖ * (((b * a * n ^ 2 : ℕ) : ℝ)) * (n : ℝ) *
          (‖(hughesYoungHeightWeight T t : ℂ)‖ *
            (((b * a * R : ℕ) : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2))) *
            ((n : ℝ) ^ (-2 : ℝ)) *
            (2312 * max 1
              (((1 / hughesYoungDyadicRatio) / (n : ℝ)) ^
                (-(3 / 4 : ℝ))) + 72)) *
          (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
            (hughesYoungEquation84LogBudget b a n +
              4 * Real.log (q : ℝ)) ^ 2)
      have hscale :=
        integrable_norm_hughesYoungReducedMellinScaleConstantComplex_vertical_even
          hT ht hQ h k
      have hmul := hscale.const_mul C
      rw [show (fun u : ℝ =>
          hughesYoungNonLowerActiveComplementEvenSignedMajorant
            T t u Q h k a b R (Int.negSucc m)) =
          (fun u : ℝ => C *
            ‖hughesYoungReducedMellinScaleConstantComplex T t
              (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖) by
        funext u
        simp only [hughesYoungNonLowerActiveComplementEvenSignedMajorant,
          hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor]
        rw [hughesYoungReducedMellinScaleConstantComplex_swap]
        dsimp only [n, C]
        ring]
      exact hmul

/-- The finite sum of all exact signed-shift majorants on the opening line
is integrable. -/
theorem integrable_hughesYoungNonLowerActiveComplementEvenSourceMajorant
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) {Q : ℕ} (hQ : 0 < Q)
    (h k a b R K : ℕ) :
    Integrable (fun u : ℝ =>
      ∑ r ∈ hughesYoungShiftInterval a b
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        if r = 0 then 0 else
          hughesYoungNonLowerActiveComplementEvenSignedMajorant
            T t u Q h k a b R r) := by
  let S := hughesYoungShiftInterval a b
    (hughesYoungFullDyadicBound (K + 1))
    (hughesYoungFullDyadicBound (K + 1))
  apply integrable_finsetSum S
  intro r _hr
  by_cases hr0 : r = 0
  · simp [hr0]
  · simpa only [hr0, if_false] using
      integrable_hughesYoungNonLowerActiveComplementEvenSignedMajorant
        hT ht hQ h k a b R r

/-- The literal non-lower signed source is integrable on the genuine even
opening line. -/
theorem integrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (h k : ℕ) :
    Integrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K) := by
  apply (integrable_hughesYoungNonLowerActiveComplementEvenSourceMajorant
    hT ht hQ h k a b R K).mono'
    (aestronglyMeasurable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even
      ha hb hR hstrong hQ t h k)
  filter_upwards with u
  exact
    norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_even_le
      ha hb hR hstrong hQ t u h k

/-- Symmetric opening-line intervals exhaust the genuine whole-line
Bochner integral. -/
theorem tendsto_intervalIntegral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (h k : ℕ) :
    Tendsto (fun H : ℝ =>
      ∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k a b R K)
      atTop (nhds (∫ u : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k a b R K)) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even
      hT ht ha hb hR hstrong hQ h k)
    tendsto_neg_atTop_atBot tendsto_id

/-- Moving the literal non-lower source from a positive source line to the
even opening line identifies the limit of its symmetric source-line
integrals with the genuine opening-line integral. -/
theorem tendsto_intervalIntegral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_source_to_even
    {T c₀ : ℝ} (hT : 1 ≤ T) (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    {t : ℝ} (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (h k : ℕ) :
    Tendsto (fun H : ℝ =>
      ∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K)
      atTop (nhds (∫ u : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k a b R K)) := by
  have hopen :=
    tendsto_intervalIntegral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even
      hT ht ha hb hR hstrong hQ h k
  have hdiff :=
    tendsto_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_sub_zero_even
      hc₀ hc₀one ha hb hR hstrong hQ t h k (T := T)
  have hsub := hopen.sub hdiff
  simpa only [sub_zero, sub_sub_cancel] using hsub

/-- The norm of the complete opening-line integral is controlled by the
integral of the exact finite signed-shift majorant. -/
theorem norm_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even_le
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (h k : ℕ) :
    ‖∫ u : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k a b R K‖ ≤
      ∫ u : ℝ,
        ∑ r ∈ hughesYoungShiftInterval a b
            (hughesYoungFullDyadicBound (K + 1))
            (hughesYoungFullDyadicBound (K + 1)),
          if r = 0 then 0 else
            hughesYoungNonLowerActiveComplementEvenSignedMajorant
              T t u Q h k a b R r := by
  apply MeasureTheory.norm_integral_le_of_norm_le
    (integrable_hughesYoungNonLowerActiveComplementEvenSourceMajorant
      hT ht hQ h k a b R K)
  filter_upwards with u
  exact
    norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_even_le
      ha hb hR hstrong hQ t u h k

/-- Exact finite-height solved rectangle identity.  It is the quantitative
form used at the physical truncation `H = T/8`: the source interval equals
the opening interval after adding the two horizontal-edge corrections. -/
theorem intervalIntegral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_sub_eq_horizontal_even
    {T c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) {H : ℝ} (hH : 1 ≤ H)
    (h k : ℕ) :
    (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k a b R K) -
      (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K) =
      (-I) *
        ((∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementSignedSourceComplex
                T t ((s : ℂ) + (H : ℂ) * I) h k a b R K) -
          (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementSignedSourceComplex
                T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K)) := by
  have hc : c₀ ≤ ((2 * Q : ℕ) : ℝ) := by
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    push_cast
    linarith
  let F : ℂ → ℂ := fun w =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementSignedSourceComplex
        T t w h k a b R K
  have hrect :=
    heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_boundaryRect_zero_even
      hc₀ hc₀one ha hb hR hstrong hQ t hH h k (T := T)
  change
    (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        F ((s : ℂ) + ((-H : ℝ) : ℂ) * I)) -
      (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        F ((s : ℂ) + (H : ℂ) * I)) +
      I • (∫ u : ℝ in -H..H,
        F (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)) -
      I • (∫ u : ℝ in -H..H,
        F ((c₀ : ℂ) + (u : ℂ) * I)) = 0 at hrect
  rw [smul_eq_mul, smul_eq_mul] at hrect
  have hI :
      I * ((∫ u : ℝ in -H..H,
          F (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)) -
        (∫ u : ℝ in -H..H, F ((c₀ : ℂ) + (u : ℂ) * I))) =
        (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
          F ((s : ℂ) + (H : ℂ) * I)) -
        (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
          F ((s : ℂ) + ((-H : ℝ) : ℂ) * I)) := by
    linear_combination hrect
  change
    (∫ u : ℝ in -H..H,
        F (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)) -
      (∫ u : ℝ in -H..H, F ((c₀ : ℂ) + (u : ℂ) * I)) = _
  rw [← hI, ← mul_assoc]
  have hnegI : (-I : ℂ) * I = 1 := by
    rw [neg_mul, I_mul_I]
    simp
  rw [hnegI, one_mul]

end RiemannZeta.GuthMaynard

import RiemannZeta.GuthMaynard.HughesYoungSmallContourJoint
import RiemannZeta.GuthMaynard.HughesYoungSmallContourQuantitative

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Integrated small-contour tail

This file passes the fixed-height Gaussian estimate for the literal finite
equation-(84) source through the physical-height integral.  The joint
measurability proved in `HughesYoungSmallContourJoint` is used explicitly;
the outer integral is not manipulated before its Bochner integrability has
been established.
-/

private noncomputable def hughesYoungPureCentralIntegrand
    (T c : ℝ) (h k a b K : ℕ) (p : ℝ × ℝ) : ℂ :=
  (hughesYoungHeightWeight T p.1 : ℂ) *
    hughesYoungFinitePureSignedCentralAtHeight
      T p.1 c p.2 h k a b K

private noncomputable def hughesYoungPureCentralWholeAtHeight
    (T c : ℝ) (h k a b K : ℕ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, hughesYoungPureCentralIntegrand T c h k a b K (t, u)

private noncomputable def hughesYoungPureCentralFiniteAtHeight
    (T c H : ℝ) (h k a b K : ℕ) (t : ℝ) : ℂ :=
  ∫ u in -H..H, hughesYoungPureCentralIntegrand T c h k a b K (t, u)

theorem aestronglyMeasurable_hughesYoungPureCentralWholeAtHeight
    (T : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    AEStronglyMeasurable
      (hughesYoungPureCentralWholeAtHeight T c h k a b K) := by
  have hjoint :=
    aestronglyMeasurable_uncurry_hughesYoungFinitePureSignedCentralAtHeight
      (μ := volume) (ν := volume) T hc hcHalf hh hk ha hb K
  exact hjoint.integral_prod_right'

theorem aestronglyMeasurable_hughesYoungPureCentralFiniteAtHeight
    (T : ℝ) {c H : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (hH : 0 ≤ H) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    AEStronglyMeasurable
      (hughesYoungPureCentralFiniteAtHeight T c H h k a b K) := by
  have hjoint :=
    aestronglyMeasurable_uncurry_hughesYoungFinitePureSignedCentralAtHeight
      (μ := volume) (ν := volume.restrict (Set.Ioc (-H) H))
      T hc hcHalf hh hk ha hb K
  have hrestricted : AEStronglyMeasurable (fun t : ℝ =>
      ∫ u : ℝ, hughesYoungPureCentralIntegrand T c h k a b K (t, u)
        ∂(volume.restrict (Set.Ioc (-H) H))) :=
    hjoint.integral_prod_right'
  change AEStronglyMeasurable (fun t : ℝ =>
    ∫ u in -H..H, hughesYoungPureCentralIntegrand T c h k a b K (t, u))
  simpa only [intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
    using hrestricted

theorem integrable_hughesYoungPureCentralWholeAtHeight
    {C D T : ℝ} {h k K : ℕ}
    (hD : 0 < D)
    (hsource : ∀ {T t u : ℝ} {h k K : ℕ},
      Real.exp 4 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
      4 * C * hughesYoungSmallContour T ≤ 1 →
      0 < h → 0 < k →
      ‖hughesYoungFinitePureSignedCentralAtHeight T t
          (hughesYoungSmallContour T) u h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K‖ ≤
        hughesYoungFiniteSmallContourShiftMass T h k K *
          (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
            (1 + |u|) ^ 17))
    (hT : Real.exp 4 ≤ T)
    (hcontour : 4 * C * hughesYoungSmallContour T ≤ 1)
    (hh : 0 < h) (hk : 0 < k) :
    Integrable (hughesYoungPureCentralWholeAtHeight T
      (hughesYoungSmallContour T) h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K) := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  obtain ⟨hc, _hcOne, _⟩ := hughesYoungSmallContour_spec hT1
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hcHalf : hughesYoungSmallContour T < 1 / 2 := by
    unfold hughesYoungSmallContour
    have hlog0 : 0 < Real.log T := (by norm_num : (0 : ℝ) < 4).trans_le hlog4
    calc
      (Real.log T)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlog4
      _ < 1 / 2 := by norm_num
  let p : ℝ → ℝ := fun u => Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17
  let A : ℝ := hughesYoungFiniteSmallContourShiftMass T h k K *
    (D * T ^ (4 : ℕ))
  let B : ℝ := A * ∫ u : ℝ, p u
  let g : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => B)
  have hp : Integrable p := integrable_exp_neg_84_mul_one_add_abs_pow 17
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (hughesYoungFiniteSmallContourShiftMass_nonneg T h k K)
      (mul_nonneg hD.le (by positivity))
  have hpInt : 0 ≤ ∫ u : ℝ, p u := integral_nonneg fun _ => by
    dsimp only [p]
    positivity
  have hB : 0 ≤ B := mul_nonneg hA hpInt
  have hg : Integrable g := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hmeas :=
    aestronglyMeasurable_hughesYoungPureCentralWholeAtHeight
      T hc hcHalf hh hk
        (hughesYoungReducedLeft_pos (k := k) hh)
        (hughesYoungReducedRight_pos hh hk) K
  refine hg.mono' hmeas ?_
  filter_upwards [] with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · have hzero : hughesYoungPureCentralWholeAtHeight T
        (hughesYoungSmallContour T) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t = 0 := by
      unfold hughesYoungPureCentralWholeAtHeight
      simp [hughesYoungPureCentralIntegrand, hw]
    rw [hzero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hB) t
  · have ht := hughesYoungHeightWeight_support ((Real.exp_pos 4).trans_le hT) hw
    have htAbs : |t| ∈ Set.Icc (T / 4) (4 * T) := by
      have ht0 : 0 ≤ t := (div_nonneg ((Real.exp_pos 4).trans_le hT).le
        (by norm_num)).trans ht.1
      simpa [abs_of_nonneg ht0] using ht
    have hw0 := hughesYoungHeightWeight_nonneg T t
    have hw1 := hughesYoungHeightWeight_le_one T t
    have hAp : Integrable (fun u => A * p u) := hp.const_mul A
    have hinner : ‖hughesYoungPureCentralWholeAtHeight T
        (hughesYoungSmallContour T) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t‖ ≤ B := by
      unfold hughesYoungPureCentralWholeAtHeight
      apply (norm_integral_le_of_norm_le hAp ?_).trans_eq
      · rw [integral_const_mul]
      · filter_upwards [] with u
        rw [hughesYoungPureCentralIntegrand, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
        have hs := hsource hT htAbs hcontour hh hk (u := u) (K := K)
        calc
          hughesYoungHeightWeight T t *
              ‖hughesYoungFinitePureSignedCentralAtHeight T t
                (hughesYoungSmallContour T) u h k
                (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) K‖ ≤ 1 *
              (hughesYoungFiniteSmallContourShiftMass T h k K *
                (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
                  (1 + |u|) ^ 17)) := by gcongr
          _ = A * p u := by dsimp only [A, p]; ring
    dsimp only [g]
    rw [Set.indicator_of_mem ht]
    exact hinner

theorem integrable_hughesYoungPureCentralFiniteAtHeight
    {C D T H : ℝ} {h k K : ℕ}
    (hD : 0 < D)
    (hsource : ∀ {T t u : ℝ} {h k K : ℕ},
      Real.exp 4 ≤ T → |t| ∈ Set.Icc (T / 4) (4 * T) →
      4 * C * hughesYoungSmallContour T ≤ 1 →
      0 < h → 0 < k →
      ‖hughesYoungFinitePureSignedCentralAtHeight T t
          (hughesYoungSmallContour T) u h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K‖ ≤
        hughesYoungFiniteSmallContourShiftMass T h k K *
          (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
            (1 + |u|) ^ 17))
    (hT : Real.exp 4 ≤ T)
    (hcontour : 4 * C * hughesYoungSmallContour T ≤ 1)
    (hH : 1 ≤ H) (hh : 0 < h) (hk : 0 < k) :
    Integrable (hughesYoungPureCentralFiniteAtHeight T
      (hughesYoungSmallContour T) H h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K) := by
  have hwhole := integrable_hughesYoungPureCentralWholeAtHeight
    (K := K) hD hsource hT hcontour hh hk
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  obtain ⟨hc, _hcOne, _⟩ := hughesYoungSmallContour_spec hT1
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hcHalf : hughesYoungSmallContour T < 1 / 2 := by
    unfold hughesYoungSmallContour
    calc
      (Real.log T)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlog4
      _ < 1 / 2 := by norm_num
  let A : ℝ := hughesYoungFiniteSmallContourShiftMass T h k K *
    (D * T ^ (4 : ℕ)) * hughesYoungSmallContourGaussianTailConstant *
      Real.exp (-40 * H ^ 2)
  let g : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (hughesYoungFiniteSmallContourShiftMass_nonneg T h k K)
          (mul_nonneg hD.le (by positivity)))
        hughesYoungSmallContourGaussianTailConstant_pos.le)
      (Real.exp_pos _).le
  have hg : Integrable g := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hwholeMeas := hwhole.aestronglyMeasurable
  have hfiniteMeas :=
    aestronglyMeasurable_hughesYoungPureCentralFiniteAtHeight
      T hc hcHalf (zero_le_one.trans hH) hh hk
        (hughesYoungReducedLeft_pos (k := k) hh)
        (hughesYoungReducedRight_pos hh hk) K
  have hdiff : Integrable (fun t =>
      hughesYoungPureCentralWholeAtHeight T (hughesYoungSmallContour T)
          h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t -
        hughesYoungPureCentralFiniteAtHeight T (hughesYoungSmallContour T) H
          h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t) := by
    refine hg.mono' (hwholeMeas.sub hfiniteMeas) ?_
    filter_upwards [] with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · have hwholeZero : hughesYoungPureCentralWholeAtHeight T
          (hughesYoungSmallContour T) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t = 0 := by
        unfold hughesYoungPureCentralWholeAtHeight
        simp [hughesYoungPureCentralIntegrand, hw]
      have hfiniteZero : hughesYoungPureCentralFiniteAtHeight T
          (hughesYoungSmallContour T) H h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t = 0 := by
        unfold hughesYoungPureCentralFiniteAtHeight
        simp [hughesYoungPureCentralIntegrand, hw]
      rw [hwholeZero, hfiniteZero, sub_zero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hA) t
    · have ht := hughesYoungHeightWeight_support ((Real.exp_pos 4).trans_le hT) hw
      have htAbs : |t| ∈ Set.Icc (T / 4) (4 * T) := by
        have ht0 : 0 ≤ t := (div_nonneg ((Real.exp_pos 4).trans_le hT).le
          (by norm_num)).trans ht.1
        simpa [abs_of_nonneg ht0] using ht
      have hfixed :
          ‖hughesYoungPureCentralWholeAtHeight T
                (hughesYoungSmallContour T) h k
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t -
              hughesYoungPureCentralFiniteAtHeight T
                (hughesYoungSmallContour T) H h k
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t‖ ≤ A := by
        unfold hughesYoungPureCentralWholeAtHeight
          hughesYoungPureCentralFiniteAtHeight hughesYoungPureCentralIntegrand
        have hf := integrable_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight
          (T := T) (h := h) (k := k)
          (a := hughesYoungReducedLeft h k)
          (b := hughesYoungReducedRight h k)
          hc hcHalf t (hughesYoungReducedLeft_pos hh)
            (hughesYoungReducedRight_pos hh hk) K
        have htailDirect := norm_integral_sub_symmetricIntervalIntegral_le_compl_norm
          hf (zero_le_one.trans hH)
        let p : ℝ → ℝ := fun u => Real.exp (-84 * u ^ 2) * (1 + |u|) ^ 17
        let B : ℝ := hughesYoungFiniteSmallContourShiftMass T h k K *
          (D * T ^ (4 : ℕ))
        have hp : Integrable p := integrable_exp_neg_84_mul_one_add_abs_pow 17
        have hB : 0 ≤ B := by
          dsimp only [B]
          exact mul_nonneg
            (hughesYoungFiniteSmallContourShiftMass_nonneg T h k K)
            (mul_nonneg hD.le (by positivity))
        have hBp : Integrable (fun u => B * p u) := hp.const_mul B
        calc
          _ ≤ ∫ u in (Set.Ioc (-H) H)ᶜ,
              ‖(hughesYoungHeightWeight T t : ℂ) *
                hughesYoungFinitePureSignedCentralAtHeight T t
                  (hughesYoungSmallContour T) u h k
                  (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) K‖ := htailDirect
          _ ≤ ∫ u in (Set.Ioc (-H) H)ᶜ, B * p u := by
            apply MeasureTheory.setIntegral_mono_on hf.norm.integrableOn
              hBp.integrableOn measurableSet_Ioc.compl
            intro u _hu
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)]
            have hs := hsource hT htAbs hcontour hh hk (u := u) (K := K)
            calc
              hughesYoungHeightWeight T t *
                  ‖hughesYoungFinitePureSignedCentralAtHeight T t
                    (hughesYoungSmallContour T) u h k
                    (hughesYoungReducedLeft h k)
                    (hughesYoungReducedRight h k) K‖ ≤ 1 *
                  (hughesYoungFiniteSmallContourShiftMass T h k K *
                    (D * T ^ (4 : ℕ) * Real.exp (-84 * u ^ 2) *
                      (1 + |u|) ^ 17)) := by
                gcongr
                exact hughesYoungHeightWeight_le_one T t
              _ = B * p u := by dsimp only [B, p]; ring
          _ ≤ B * (hughesYoungSmallContourGaussianTailConstant *
                Real.exp (-40 * H ^ 2)) := by
            rw [MeasureTheory.integral_const_mul]
            gcongr
            exact integral_compl_Ioc_exp_neg84_mul_one_add_abs_pow_seventeen_le hH
          _ = A := by dsimp only [A, B]; ring
      dsimp only [g]
      rw [Set.indicator_of_mem ht]
      exact hfixed
  have hfiniteEq : hughesYoungPureCentralFiniteAtHeight T
      (hughesYoungSmallContour T) H h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K =
      fun t => hughesYoungPureCentralWholeAtHeight T (hughesYoungSmallContour T)
          h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t -
        (hughesYoungPureCentralWholeAtHeight T (hughesYoungSmallContour T)
          h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t -
        hughesYoungPureCentralFiniteAtHeight T (hughesYoungSmallContour T) H
          h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K t) := by
    funext t
    ring
  rw [hfiniteEq]
  exact hwhole.sub hdiff

/-- The literal finite small-contour tail, after both mollifier sums and the
physical-height integration, has the Gaussian loss predicted by the
Hughes--Young contour truncation. -/
theorem exists_norm_hughesYoungFinitePureSmallContourTail_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T : ℝ}, Real.exp 4 ≤ T → 16 ≤ T →
        4 * C * hughesYoungSmallContour T ≤ 1 →
        ‖hughesYoungFinitePureSmallContourTail T
            (hughesYoungGlobalDepth T)‖ ≤
          (15 * T / 4) * hughesYoungTerminalSmallContourTotalMass T *
            (D * T ^ (4 : ℕ)) *
              hughesYoungSmallContourGaussianTailConstant *
                Real.exp (-40 * (T / 8) ^ 2) := by
  obtain ⟨C₀, D₀, hC₀, hD₀, hsource⟩ :=
    exists_norm_hughesYoungFinitePureSignedCentralAtHeight_smallContour_le
  obtain ⟨C₁, D₁, hC₁, hD₁, hpoint⟩ :=
    exists_norm_hughesYoungFinitePureContourTailAtHeight_le
  refine ⟨C₀ + C₁, D₁, add_pos hC₀ hC₁, hD₁, ?_⟩
  intro T hT hT16 hcontour
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hc0 : 0 ≤ hughesYoungSmallContour T :=
    (hughesYoungSmallContour_spec hT1).1.le
  have hcontour₀ : 4 * C₀ * hughesYoungSmallContour T ≤ 1 := by
    calc
      4 * C₀ * hughesYoungSmallContour T ≤
          4 * (C₀ + C₁) * hughesYoungSmallContour T := by
            gcongr
            exact le_add_of_nonneg_right hC₁.le
      _ ≤ 1 := hcontour
  have hcontour₁ : 4 * C₁ * hughesYoungSmallContour T ≤ 1 := by
    calc
      4 * C₁ * hughesYoungSmallContour T ≤
          4 * (C₀ + C₁) * hughesYoungSmallContour T := by
            gcongr
            exact le_add_of_nonneg_left hC₀.le
      _ ≤ 1 := hcontour
  have hH : 1 ≤ T / 8 := by linarith
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let E : ℝ := (D₁ * T ^ (4 : ℕ)) *
    hughesYoungSmallContourGaussianTailConstant *
      Real.exp (-40 * (T / 8) ^ 2)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hD₁.le (by positivity))
        hughesYoungSmallContourGaussianTailConstant_pos.le)
      (Real.exp_pos _).le
  have hpair : ∀ h ∈ S, ∀ k ∈ S,
      ‖(∫ t : ℝ,
            hughesYoungPureCentralWholeAtHeight T
              (hughesYoungSmallContour T) h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k)
              (hughesYoungGlobalDepth T) t) -
          ∫ t : ℝ,
            hughesYoungPureCentralFiniteAtHeight T
              (hughesYoungSmallContour T) (T / 8) h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k)
              (hughesYoungGlobalDepth T) t‖ ≤
        (15 * T / 4) *
          (hughesYoungFiniteSmallContourShiftMass T h k
            (hughesYoungGlobalDepth T) * E) := by
    intro h hh k hk
    have hhpos : 0 < h := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hh).1
    have hkpos : 0 < k := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1
    have hwhole := integrable_hughesYoungPureCentralWholeAtHeight
      (K := hughesYoungGlobalDepth T) hD₀ hsource hT hcontour₀ hhpos hkpos
    have hfinite := integrable_hughesYoungPureCentralFiniteAtHeight
      (K := hughesYoungGlobalDepth T) hD₀ hsource hT hcontour₀ hH hhpos hkpos
    let A : ℝ := hughesYoungFiniteSmallContourShiftMass T h k
      (hughesYoungGlobalDepth T) * E
    let g : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
    have hA : 0 ≤ A := mul_nonneg
      (hughesYoungFiniteSmallContourShiftMass_nonneg T h k
        (hughesYoungGlobalDepth T)) hE
    have hg : Integrable g := by
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const isCompact_Icc.measure_ne_top
    rw [← integral_sub hwhole hfinite]
    apply (norm_integral_le_of_norm_le hg ?_).trans_eq
    · rw [show (∫ t : ℝ, g t) = ∫ _t in Set.Icc (T / 4) (4 * T), A by
          exact MeasureTheory.integral_indicator measurableSet_Icc]
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
      ring
    · filter_upwards [] with t
      by_cases hw : hughesYoungHeightWeight T t = 0
      · have hwholeZero : hughesYoungPureCentralWholeAtHeight T
            (hughesYoungSmallContour T) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungGlobalDepth T) t = 0 := by
          unfold hughesYoungPureCentralWholeAtHeight
          simp [hughesYoungPureCentralIntegrand, hw]
        have hfiniteZero : hughesYoungPureCentralFiniteAtHeight T
            (hughesYoungSmallContour T) (T / 8) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungGlobalDepth T) t = 0 := by
          unfold hughesYoungPureCentralFiniteAtHeight
          simp [hughesYoungPureCentralIntegrand, hw]
        rw [hwholeZero, hfiniteZero, sub_zero, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hA) t
      · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
          hughesYoungHeightWeight_support ((Real.exp_pos 4).trans_le hT) hw
        have htAbs : |t| ∈ Set.Icc (T / 4) (4 * T) := by
          have ht0 : 0 ≤ t := (div_nonneg ((Real.exp_pos 4).trans_le hT).le
            (by norm_num)).trans ht.1
          simpa [abs_of_nonneg ht0] using ht
        have hp := hpoint hT htAbs hcontour₁ hhpos hkpos hH
          (K := hughesYoungGlobalDepth T)
        change ‖hughesYoungPureCentralWholeAtHeight T
              (hughesYoungSmallContour T) h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungGlobalDepth T) t -
            hughesYoungPureCentralFiniteAtHeight T
              (hughesYoungSmallContour T) (T / 8) h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungGlobalDepth T) t‖ ≤ g t
        dsimp only [g]
        rw [Set.indicator_of_mem ht]
        simpa only [hughesYoungPureCentralWholeAtHeight,
          hughesYoungPureCentralFiniteAtHeight, hughesYoungPureCentralIntegrand,
          A, E, mul_assoc] using hp
  unfold hughesYoungFinitePureSmallContourTail
    hughesYoungFinitePureWholeIntegratedCentral
    hughesYoungFinitePureIntegratedCentral
  change ‖(∑ h ∈ S, ∑ k ∈ S,
      ∫ t : ℝ, hughesYoungPureCentralWholeAtHeight T
        (hughesYoungSmallContour T) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungGlobalDepth T) t) -
      ∑ h ∈ S, ∑ k ∈ S,
      ∫ t : ℝ, hughesYoungPureCentralFiniteAtHeight T
        (hughesYoungSmallContour T) (T / 8) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungGlobalDepth T) t‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ h ∈ S, ∑ k ∈ S,
        ((∫ t : ℝ, hughesYoungPureCentralWholeAtHeight T
            (hughesYoungSmallContour T) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungGlobalDepth T) t) -
          ∫ t : ℝ, hughesYoungPureCentralFiniteAtHeight T
            (hughesYoungSmallContour T) (T / 8) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungGlobalDepth T) t)‖
        ≤ ∑ h ∈ S, ∑ k ∈ S,
            ‖(∫ t : ℝ, hughesYoungPureCentralWholeAtHeight T
                (hughesYoungSmallContour T) h k
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
                (hughesYoungGlobalDepth T) t) -
              ∫ t : ℝ, hughesYoungPureCentralFiniteAtHeight T
                (hughesYoungSmallContour T) (T / 8) h k
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
                (hughesYoungGlobalDepth T) t‖ := by
          exact (norm_sum_le _ _).trans <|
            Finset.sum_le_sum fun h _ => norm_sum_le _ _
    _ ≤ ∑ h ∈ S, ∑ k ∈ S,
          (15 * T / 4) *
            (hughesYoungFiniteSmallContourShiftMass T h k
              (hughesYoungGlobalDepth T) * E) := by
          gcongr with h hh k hk
          exact hpair h hh k hk
    _ = (15 * T / 4) *
          ((∑ h ∈ S, ∑ k ∈ S,
            hughesYoungFiniteSmallContourShiftMass T h k
              (hughesYoungGlobalDepth T)) * E) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
    _ = (15 * T / 4) * hughesYoungTerminalSmallContourTotalMass T *
          (D₁ * T ^ (4 : ℕ)) *
            hughesYoungSmallContourGaussianTailConstant *
              Real.exp (-40 * (T / 8) ^ 2) := by
          simp only [hughesYoungTerminalSmallContourTotalMass, S, E]
          ring

/-- The integrated finite small-contour tail is negligible at the native
Hughes--Young fourth-moment scale. -/
theorem hughesYoungFinitePureSmallContourTail_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungFinitePureSmallContourTail T
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, D, hC, hD, htail⟩ :=
    exists_norm_hughesYoungFinitePureSmallContourTail_le
  let M : ℝ := 12 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungEquation84LogProfileMass * 9 ^ (11 : ℕ) * 7 ^ (5 : ℕ)
  let A : ℝ := (15 / 4 : ℝ) * M * D *
    hughesYoungSmallContourGaussianTailConstant
  have hM : 0 ≤ M := by
    have hprofile : 0 ≤ hughesYoungEquation84LogProfileMass :=
      hughesYoungEquation84LogProfileMass_pos.le
    dsimp only [M]
    positivity
  have hA : 0 ≤ A := by
    have hgauss : 0 ≤ hughesYoungSmallContourGaussianTailConstant :=
      hughesYoungSmallContourGaussianTailConstant_pos.le
    dsimp only [A]
    positivity
  have hbaseRpow : Tendsto (fun T : ℝ =>
      T ^ (527 : ℝ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2))
      atTop (nhds 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 5 / 8) 527).tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg
            (by norm_num : (-(1 / 2 : ℝ)) < 0)))
  have hbase : Tendsto (fun T : ℝ =>
      T ^ (527 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2))
      atTop (nhds 0) := by
    simpa only [← Real.rpow_natCast] using hbaseRpow
  have hlimit : Tendsto (fun T : ℝ =>
      A * (T ^ (527 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hbase.const_mul A
  have hsmall : ∀ᶠ T : ℝ in atTop,
      A * (T ^ (527 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)) ≤ 1 :=
    (hlimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      fun _ h => h.le
  apply IsBigO.of_bound 1
  filter_upwards [hsmall,
      eventually_ge_atTop (max (max (Real.exp 4) 16) (Real.exp (4 * C)))]
      with T hsmallT hT
  have hTexp4 : Real.exp 4 ≤ T :=
    ((le_max_left (Real.exp 4) 16).trans
      (le_max_left (max (Real.exp 4) 16) (Real.exp (4 * C)))).trans hT
  have hT16 : 16 ≤ T :=
    ((le_max_right (Real.exp 4) 16).trans
      (le_max_left (max (Real.exp 4) 16) (Real.exp (4 * C)))).trans hT
  have hTexpC : Real.exp (4 * C) ≤ T :=
    (le_max_right (max (Real.exp 4) 16) (Real.exp (4 * C))).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hlog : 4 * C ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos (4 * C)) hTexpC
  have hlog0 : 0 < Real.log T := by
    have : 0 < 4 * C := mul_pos (by norm_num) hC
    linarith
  have hcontour : 4 * C * hughesYoungSmallContour T ≤ 1 := by
    unfold hughesYoungSmallContour
    calc
      4 * C * (Real.log T)⁻¹ ≤ Real.log T * (Real.log T)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hlog0.le)
      _ = 1 := mul_inv_cancel₀ hlog0.ne'
  have hmass :=
    hughesYoungTerminalSmallContourTotalMass_le_pow_fiveHundredTwentyTwo hTexp4
  have hraw := htail hTexp4 hT16 hcontour
  have hgauss : 0 ≤ hughesYoungSmallContourGaussianTailConstant :=
    hughesYoungSmallContourGaussianTailConstant_pos.le
  have hbound :
      ‖hughesYoungFinitePureSmallContourTail T
          (hughesYoungGlobalDepth T)‖ ≤
        A * (T ^ (527 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)) := by
    calc
      _ ≤ (15 * T / 4) * hughesYoungTerminalSmallContourTotalMass T *
            (D * T ^ (4 : ℕ)) *
              hughesYoungSmallContourGaussianTailConstant *
                Real.exp (-40 * (T / 8) ^ 2) := hraw
      _ ≤ (15 * T / 4) * (M * T ^ (522 : ℕ)) *
            (D * T ^ (4 : ℕ)) *
              hughesYoungSmallContourGaussianTailConstant *
                Real.exp (-40 * (T / 8) ^ 2) := by
            gcongr
      _ = A * (T ^ (527 : ℕ) *
            Real.exp (-(5 / 8 : ℝ) * T ^ 2)) := by
            dsimp only [A]
            ring_nf
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungFinitePureSmallContourTail T
        (hughesYoungGlobalDepth T))), htarget]
  have hone : 1 ≤ 1 * T ^ (1 + ε) := by
    simpa using Real.one_le_rpow hT1 (show 0 ≤ 1 + ε by linarith)
  exact hbound.trans (hsmallT.trans hone)

end RiemannZeta.GuthMaynard

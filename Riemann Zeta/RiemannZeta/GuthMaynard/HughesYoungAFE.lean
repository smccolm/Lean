import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannZeta.GuthMaynard.DFITheorem1
import RiemannZeta.GuthMaynard.HughesYoungMoment
import RiemannZeta.GuthMaynard.SmoothZetaAFE

open Complex Filter MeasureTheory Set TopologicalSpace Topology
open scoped BigOperators Interval LSeries.notation

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Arithmetic opening of the unshifted Hughes--Young AFE

The completed-zeta contour in `SmoothZetaAFE` is opened here on a right
line where both divisor Dirichlet series converge absolutely.  This file
records the exact pair-indexed series and the summability data required for
the later Mellin/height Fubini arguments.
-/

/-- One term of the ordinary divisor Dirichlet series. -/
noncomputable def divisorDirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun k : ℕ => (k.divisors.card : ℂ)) s n

/-- On positive indices the opened divisor series is literally the DFI
divisor coefficient times the corresponding complex power. -/
theorem divisorDirichletTerm_eq_divisorWeight_mul_cpow
    (s : ℂ) (n : ℕ) :
    divisorDirichletTerm s n =
      divisorWeight n * (n : ℂ) ^ (-s) := by
  unfold divisorDirichletTerm divisorWeight
  rw [LSeries.term_def₀]
  simp

theorem summable_divisorDirichletTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (divisorDirichletTerm s) := by
  exact divisorLSeries_summable hs

theorem tsum_divisorDirichletTerm (s : ℂ) :
    ∑' n : ℕ, divisorDirichletTerm s n =
      LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s := rfl

/-- The absolutely convergent two-dimensional divisor series produced by
the product of the two zeta squares on a right contour. -/
theorem divisorLSeries_mul_eq_tsum_pair
    {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re) (hs₂ : 1 < s₂.re) :
    LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s₁ *
        LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s₂ =
      ∑' p : ℕ × ℕ,
        divisorDirichletTerm s₁ p.1 * divisorDirichletTerm s₂ p.2 := by
  exact (summable_divisorDirichletTerm hs₁).tsum_mul_tsum
    (summable_divisorDirichletTerm hs₂)
    (summable_mul_of_summable_norm
      (summable_norm_iff.mpr (summable_divisorDirichletTerm hs₁))
      (summable_norm_iff.mpr (summable_divisorDirichletTerm hs₂)))

/-- The non-arithmetic coefficient of the divisor AFE on the right line
`Re w = c`, normalized back to the ordinary zeta product. -/
noncomputable def hughesYoungRightContourWeight (t c u : ℝ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  Complex.exp (100 * w ^ 2) *
    (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2 *
    Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2 /
    afePoleNormalization t / w / afeGammaNormalization t

/-- One pair-indexed term of the opened right-contour AFE. -/
noncomputable def hughesYoungRightPairTerm
    (t c u : ℝ) (p : ℕ × ℕ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  hughesYoungRightContourWeight t c u *
    divisorDirichletTerm (afeCriticalPoint t + w) p.1 *
    divisorDirichletTerm (afeCriticalPoint (-t) + w) p.2

theorem summable_hughesYoungRightPairTerm
    (t u : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Summable (hughesYoungRightPairTerm t c u) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hs₁ : 1 < (afeCriticalPoint t + w).re := by
    simp [w, afeCriticalPoint]
    linarith
  have hs₂ : 1 < (afeCriticalPoint (-t) + w).re := by
    simp [w, afeCriticalPoint]
    linarith
  have hpairs : Summable (fun p : ℕ × ℕ =>
      divisorDirichletTerm (afeCriticalPoint t + w) p.1 *
        divisorDirichletTerm (afeCriticalPoint (-t) + w) p.2) :=
    summable_mul_of_summable_norm
      (summable_norm_iff.mpr (summable_divisorDirichletTerm hs₁))
      (summable_norm_iff.mpr (summable_divisorDirichletTerm hs₂))
  exact (hpairs.mul_left (hughesYoungRightContourWeight t c u)).congr
    (fun p => by
      simp only [hughesYoungRightPairTerm, w]
      ring)

/-- Exact pointwise opening of the normalized divisor contour into its four
arithmetic indices (two divisor factors, later multiplied by the two finite
twisting indices). -/
theorem smoothZetaSqDivisorContourIntegrand_div_gamma_eq_tsum_pair
    (t u : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    smoothZetaSqDivisorContourIntegrand t c u /
        afeGammaNormalization t =
      ∑' p : ℕ × ℕ, hughesYoungRightPairTerm t c u p := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  have hs₁ : 1 < s₁.re := by
    simp [s₁, w, afeCriticalPoint]
    linarith
  have hs₂ : 1 < s₂.re := by
    simp [s₂, w, afeCriticalPoint]
    linarith
  rw [show (∑' p : ℕ × ℕ, hughesYoungRightPairTerm t c u p) =
      hughesYoungRightContourWeight t c u *
        (∑' p : ℕ × ℕ,
          divisorDirichletTerm s₁ p.1 * divisorDirichletTerm s₂ p.2) by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro p
        simp only [hughesYoungRightPairTerm, s₁, s₂, w]
        ring]
  rw [← divisorLSeries_mul_eq_tsum_pair hs₁ hs₂]
  unfold smoothZetaSqDivisorContourIntegrand hughesYoungRightContourWeight
  dsimp only [s₁, s₂, w]
  ring

/-- Along a fixed vertical line every individual divisor Dirichlet term is
continuous in the ordinate.  This is the elementary measurability input for
the Hughes--Young Mellin/Fubini step. -/
theorem continuous_divisorDirichletTerm_vertical
    (t c : ℝ) (n : ℕ) :
    Continuous (fun u : ℝ =>
      divisorDirichletTerm
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) n) := by
  by_cases hn : n = 0
  · subst n
    simpa [divisorDirichletTerm] using
      (continuous_const : Continuous (fun _u : ℝ => (0 : ℂ)))
  · simp only [divisorDirichletTerm, LSeries.term_of_ne_zero hn]
    exact continuous_const.div₀
      (continuous_const_cpow_of_ne_zero (n : ℂ)
        (by exact_mod_cast hn) (by fun_prop))
      (fun _u => (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (by exact_mod_cast hn))))

/-- Deligne's real Gamma factor is continuous along every vertical line
contained in the open right half-plane. -/
theorem continuous_GammaR_afe_vertical
    (t : ℝ) {c : ℝ} (hc : 0 < 1 / 2 + c) :
    Continuous (fun u : ℝ =>
      Complex.Gammaℝ
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) := by
  rw [continuous_iff_continuousAt]
  intro u
  unfold Complex.Gammaℝ
  apply ContinuousAt.mul
  · exact (continuousAt_const_cpow
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp (by fun_prop)
  · apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    · intro m hm
      have hre := congrArg Complex.re hm
      simp [afeCriticalPoint] at hre
      linarith

set_option maxHeartbeats 1000000 in
/-- The normalized non-arithmetic factor in the opened AFE is continuous
on a right vertical line. -/
theorem continuous_hughesYoungRightContourWeight
    (t : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Continuous (hughesYoungRightContourWeight t c) := by
  have hgammaPlus := continuous_GammaR_afe_vertical t
    (show 0 < 1 / 2 + c by linarith)
  have hgammaMinus := continuous_GammaR_afe_vertical (-t)
    (show 0 < 1 / 2 + c by linarith)
  have hwne : ∀ u : ℝ, ((c : ℂ) + (u : ℂ) * I) ≠ 0 := by
    intro u hu
    have hre := congrArg Complex.re hu
    simp at hre
    linarith
  have hpole : afePoleNormalization t ≠ 0 := afePoleNormalization_ne_zero t
  have hgamma0 : afeGammaNormalization t ≠ 0 := afeGammaNormalization_ne_zero t
  let w : ℝ → ℂ := fun u => (c : ℂ) + (u : ℂ) * I
  let s₁ : ℝ → ℂ := fun u => afeCriticalPoint t + w u
  let s₂ : ℝ → ℂ := fun u => afeCriticalPoint (-t) + w u
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hs₁ : Continuous s₁ := continuous_const.add hw
  have hs₂ : Continuous s₂ := continuous_const.add hw
  have hwne' : ∀ u, w u ≠ 0 := by
    simpa only [w] using hwne
  have hexp : Continuous (fun u => Complex.exp (100 * (w u) ^ 2)) :=
    Complex.continuous_exp.comp (continuous_const.mul (hw.pow 2))
  have hpoly₁ : Continuous (fun u => (s₁ u * (1 - s₁ u)) ^ 2) :=
    (hs₁.mul (continuous_const.sub hs₁)).pow 2
  have hpoly₂ : Continuous (fun u => (s₂ u * (1 - s₂ u)) ^ 2) :=
    (hs₂.mul (continuous_const.sub hs₂)).pow 2
  have hgammaPair : Continuous (fun u =>
      Complex.Gammaℝ (s₁ u) ^ 2 * Complex.Gammaℝ (s₂ u) ^ 2) :=
    (hgammaPlus.pow 2).mul (hgammaMinus.pow 2)
  have hnum : Continuous (fun u =>
      Complex.exp (100 * (w u) ^ 2) *
        (s₁ u * (1 - s₁ u)) ^ 2 *
        (s₂ u * (1 - s₂ u)) ^ 2 *
        Complex.Gammaℝ (s₁ u) ^ 2 *
        Complex.Gammaℝ (s₂ u) ^ 2) := by
    simpa only [mul_assoc] using
      (((hexp.mul hpoly₁).mul hpoly₂).mul hgammaPair)
  have hweight := ((hnum.div_const (afePoleNormalization t)).div₀ hw hwne').div_const
    (afeGammaNormalization t)
  simpa only [hughesYoungRightContourWeight, w, s₁, s₂] using hweight

/-- Every pair term in the opened right-contour AFE is continuous in the
Mellin ordinate. -/
theorem continuous_hughesYoungRightPairTerm
    (t : ℝ) {c : ℝ} (hc : 1 / 2 < c) (p : ℕ × ℕ) :
    Continuous (fun u : ℝ => hughesYoungRightPairTerm t c u p) := by
  unfold hughesYoungRightPairTerm
  simpa only [mul_assoc] using
    ((continuous_hughesYoungRightContourWeight t hc).mul
      (continuous_divisorDirichletTerm_vertical t c p.1)).mul
        (continuous_divisorDirichletTerm_vertical (-t) c p.2)

/-- The norm of an individual divisor term on a vertical line depends only
on the real part. -/
theorem norm_divisorDirichletTerm_afe_vertical
    (t c u : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) n‖ =
      ‖divisorDirichletTerm (afeCriticalPoint t + (c : ℂ)) n‖ := by
  simp only [divisorDirichletTerm, LSeries.norm_term_eq]
  congr 2
  simp [afeCriticalPoint]

/-- The pair term packaged as a continuous map, so Mathlib's compact
supremum-norm form of dominated convergence applies directly. -/
noncomputable def hughesYoungRightPairContinuousMap
    (t c : ℝ) (hc : 1 / 2 < c) (p : ℕ × ℕ) : C(ℝ, ℂ) :=
  ⟨fun u => hughesYoungRightPairTerm t c u p,
    continuous_hughesYoungRightPairTerm t hc p⟩

/-- On a compact Mellin interval, the whole pair family is dominated by
one constant times the absolutely summable right-line divisor series. -/
theorem exists_compact_hughesYoungRightPair_sup_bound
    (t H : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ × ℕ,
      ‖(hughesYoungRightPairContinuousMap t c hc p).restrict
          (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : Compacts ℝ)‖ ≤
        C * ‖divisorDirichletTerm
          (afeCriticalPoint t + (c : ℂ)) p.1‖ *
          ‖divisorDirichletTerm
            (afeCriticalPoint (-t) + (c : ℂ)) p.2‖ := by
  let W : ℝ → ℝ := fun u => ‖hughesYoungRightContourWeight t c u‖
  have hWcont : Continuous W :=
    (continuous_hughesYoungRightContourWeight t hc).norm
  obtain ⟨u₀, hu₀, hmax⟩ := isCompact_uIcc.exists_isMaxOn
    nonempty_uIcc hWcont.continuousOn
  let C : ℝ := 1 + W u₀
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun p => ?_⟩
  apply (ContinuousMap.norm_le
    ((hughesYoungRightPairContinuousMap t c hc p).restrict
      (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : Compacts ℝ))
    (by positivity :
      0 ≤ C * ‖divisorDirichletTerm
        (afeCriticalPoint t + (c : ℂ)) p.1‖ *
        ‖divisorDirichletTerm
          (afeCriticalPoint (-t) + (c : ℂ)) p.2‖)).2
  intro u
  change ‖hughesYoungRightPairTerm t c u.1 p‖ ≤ _
  rw [hughesYoungRightPairTerm, norm_mul, norm_mul,
    norm_divisorDirichletTerm_afe_vertical,
    norm_divisorDirichletTerm_afe_vertical]
  have hWeight : W u.1 ≤ C := by
    exact (hmax u.2).trans (by
      dsimp [C]
      linarith)
  dsimp only [W] at hWeight
  gcongr

/-- The compact supremum norms of the full pair family are summable.  This
is the exact Tonelli hypothesis, obtained from the two absolutely convergent
divisor L-series rather than from a formal rearrangement. -/
theorem summable_hughesYoungRightPair_restrict_norm
    (t H : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Summable (fun p : ℕ × ℕ =>
      ‖(hughesYoungRightPairContinuousMap t c hc p).restrict
        (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : Compacts ℝ)‖) := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_compact_hughesYoungRightPair_sup_bound t H hc
  let s₁ : ℂ := afeCriticalPoint t + (c : ℂ)
  let s₂ : ℂ := afeCriticalPoint (-t) + (c : ℂ)
  have hs₁ : 1 < s₁.re := by
    simp [s₁, afeCriticalPoint]
    linarith
  have hs₂ : 1 < s₂.re := by
    simp [s₂, afeCriticalPoint]
    linarith
  have hpairs : Summable (fun p : ℕ × ℕ =>
      divisorDirichletTerm s₁ p.1 * divisorDirichletTerm s₂ p.2) :=
    summable_mul_of_summable_norm
      (summable_norm_iff.mpr (summable_divisorDirichletTerm hs₁))
      (summable_norm_iff.mpr (summable_divisorDirichletTerm hs₂))
  have hnorm : Summable (fun p : ℕ × ℕ =>
      ‖divisorDirichletTerm s₁ p.1‖ *
        ‖divisorDirichletTerm s₂ p.2‖) := by
    simpa only [norm_mul] using hpairs.norm
  have hmajor : Summable (fun p : ℕ × ℕ =>
      C * ‖divisorDirichletTerm s₁ p.1‖ *
        ‖divisorDirichletTerm s₂ p.2‖) := by
    simpa only [mul_assoc] using hnorm.mul_left C
  apply hmajor.of_nonneg_of_le (fun p => norm_nonneg _)
  intro p
  simpa only [s₁, s₂] using hBound p

/-- Hughes--Young's opened right-contour series may be integrated term by
term on every finite vertical segment. -/
theorem tsum_intervalIntegral_hughesYoungRightPairTerm
    (t H : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    ∑' p : ℕ × ℕ,
        ∫ u in -H..H, hughesYoungRightPairTerm t c u p =
      ∫ u in -H..H,
        ∑' p : ℕ × ℕ, hughesYoungRightPairTerm t c u p := by
  simpa only [hughesYoungRightPairContinuousMap,
    ContinuousMap.coe_mk] using
    (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (summable_hughesYoungRightPair_restrict_norm t H hc))

/-- Finite-height right-contour AFE with the Mellin integral moved inside
the absolutely convergent arithmetic pair sum. -/
theorem integral_smoothZetaSqDivisor_div_gamma_eq_tsum_pair_integral
    (t H : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    ∫ u in -H..H,
        smoothZetaSqDivisorContourIntegrand t c u /
          afeGammaNormalization t =
      ∑' p : ℕ × ℕ,
        ∫ u in -H..H, hughesYoungRightPairTerm t c u p := by
  rw [tsum_intervalIntegral_hughesYoungRightPairTerm t H hc]
  apply intervalIntegral.integral_congr
  intro u _hu
  exact smoothZetaSqDivisorContourIntegrand_div_gamma_eq_tsum_pair t u hc

/-- The normalized finite right contour is exactly the termwise-integrated
Hughes--Young divisor-pair series. -/
theorem vIntegral_smoothZetaSq_div_gamma_eq_tsum_pair_integral
    (t H : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    VIntegral' (fun w => smoothZetaSqContourIntegrand t w) c (-H) H /
        afeGammaNormalization t =
      (1 / (2 * Real.pi : ℂ)) *
        ∑' p : ℕ × ℕ,
          ∫ u in -H..H, hughesYoungRightPairTerm t c u p := by
  have hgamma : afeGammaNormalization t ≠ 0 :=
    afeGammaNormalization_ne_zero t
  calc
    VIntegral' (fun w => smoothZetaSqContourIntegrand t w) c (-H) H /
        afeGammaNormalization t =
      (1 / (2 * Real.pi : ℂ)) *
        ∫ u in -H..H,
          smoothZetaSqDivisorContourIntegrand t c u /
            afeGammaNormalization t := by
      have hint :
          (∫ u in -H..H,
              smoothZetaSqContourIntegrand t
                ((c : ℂ) + (u : ℂ) * I)) =
            ∫ u in -H..H,
              smoothZetaSqDivisorContourIntegrand t c u := by
        apply intervalIntegral.integral_congr
        intro u _hu
        exact smoothZetaSqContourIntegrand_eq_divisorContour t u hc
      unfold VIntegral' VIntegral
      simp only [smul_eq_mul]
      rw [intervalIntegral.integral_div, hint]
      field_simp [Real.pi_ne_zero, hgamma]
    _ = (1 / (2 * Real.pi : ℂ)) *
        ∑' p : ℕ × ℕ,
          ∫ u in -H..H, hughesYoungRightPairTerm t c u p := by
      rw [integral_smoothZetaSqDivisor_div_gamma_eq_tsum_pair_integral
        t H hc]

/-- The opened Hughes--Young divisor-pair series converges to one half of
the two critical-line zeta squares.  This is the exact AFE limit consumed by
the mollifier expansion below. -/
theorem tendsto_hughesYoungRightPairSeries
    (t : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (fun H : ℝ =>
      (1 / (2 * Real.pi : ℂ)) *
        ∑' p : ℕ × ℕ,
          ∫ u in -H..H, hughesYoungRightPairTerm t c u p)
      atTop (𝓝 ((riemannZeta (afeCriticalPoint t) ^ 2 *
        riemannZeta (afeCriticalPoint (-t)) ^ 2) / 2)) := by
  have hafe := smoothZetaSqAFE_zeta_vertical_limit_native t
    (show 0 < c by linarith)
  exact hafe.congr' (Filter.Eventually.of_forall fun H =>
    vIntegral_smoothZetaSq_div_gamma_eq_tsum_pair_integral
      t H hc)

/-- Twice the opened right-contour series, i.e. the ordinary unshifted
zeta-square product before inserting the finite mollifier. -/
noncomputable def hughesYoungFiniteZetaProduct
    (t c H : ℝ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
    ∑' p : ℕ × ℕ,
      ∫ u in -H..H, hughesYoungRightPairTerm t c u p

theorem tendsto_hughesYoungFiniteZetaProduct
    (t : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (hughesYoungFiniteZetaProduct t c) atTop
      (𝓝 (riemannZeta (afeCriticalPoint t) ^ 2 *
        riemannZeta (afeCriticalPoint (-t)) ^ 2)) := by
  have h := (tendsto_hughesYoungRightPairSeries t hc).const_mul (2 : ℂ)
  rw [show hughesYoungFiniteZetaProduct t c = fun H : ℝ =>
      (2 : ℂ) * ((1 / (2 * Real.pi : ℂ)) *
        ∑' p : ℕ × ℕ,
          ∫ u in -H..H, hughesYoungRightPairTerm t c u p) by
    funext H
    unfold hughesYoungFiniteZetaProduct
    ring]
  convert h using 1
  congr 1
  ring

/-!
## Entry of the actual Maynard--Pratt mollifier

The Hughes--Young calculation is applied to the product at the two conjugate
critical points.  The next identities make that conjugation and the resulting
fourth-power product literal before either Dirichlet series is opened.
-/

/-- The finite Möbius polynomial commutes with complex conjugation. -/
theorem shortMobiusPolynomial_conj (T : ℝ) (s : ℂ) :
    shortMobiusPolynomial T (star s) =
      star (shortMobiusPolynomial T s) := by
  unfold shortMobiusPolynomial
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [star_mul]
  have hmPos : 0 < m := (Finset.mem_Ico.mp hm).1
  have hmArg : ((m : ℂ)).arg ≠ Real.pi := by
    change ((((m : ℝ) : ℂ)).arg ≠ Real.pi)
    rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ m)]
    exact Real.pi_ne_zero.symm
  have hpow := Complex.cpow_conj (m : ℂ) (-s) hmArg
  simp only [map_neg, map_natCast] at hpow
  calc
    (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-star s) =
        (ArithmeticFunction.moebius m : ℂ) *
          star ((m : ℂ) ^ (-s)) := by
            simpa only [starRingEnd_apply] using congrArg
              (fun z : ℂ => (ArithmeticFunction.moebius m : ℂ) * z) hpow
    _ = star ((m : ℂ) ^ (-s)) *
        star (ArithmeticFunction.moebius m : ℂ) := by
          rw [star_intCast]
          ring

/-- The two critical points used by the unshifted AFE are conjugate. -/
theorem afeCriticalPoint_neg_eq_star (t : ℝ) :
    afeCriticalPoint (-t) = star (afeCriticalPoint t) := by
  simp [afeCriticalPoint]

/-- Zeta at the lower critical point is the conjugate of zeta at the upper
critical point. -/
theorem riemannZeta_afeCriticalPoint_neg_eq_star (t : ℝ) :
    riemannZeta (afeCriticalPoint (-t)) =
      star (riemannZeta (afeCriticalPoint t)) := by
  rw [afeCriticalPoint_neg_eq_star]
  apply riemannZeta_conj
  intro h
  have hre := congrArg Complex.re h
  simp [afeCriticalPoint] at hre

/-- The Maynard--Pratt mollifier at the lower critical point is the conjugate
of the mollifier at the upper critical point. -/
theorem shortMobiusPolynomial_afeCriticalPoint_neg_eq_star (T t : ℝ) :
    shortMobiusPolynomial T (afeCriticalPoint (-t)) =
      star (shortMobiusPolynomial T (afeCriticalPoint t)) := by
  rw [afeCriticalPoint_neg_eq_star, shortMobiusPolynomial_conj]

/-- Exact complex product underlying the real fourth-power integrand.  This
is the source entry that lets the two squared mollifier sums multiply the two
zeta-square factors of the Hughes--Young AFE. -/
theorem ofReal_twistedZetaMomentIntegrand_eq_conjugate_product
    (T t : ℝ) :
    (twistedZetaMomentIntegrand T t : ℂ) =
      shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
        shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
        riemannZeta (afeCriticalPoint t) ^ 2 *
        riemannZeta (afeCriticalPoint (-t)) ^ 2 := by
  rw [shortMobiusPolynomial_afeCriticalPoint_neg_eq_star,
    riemannZeta_afeCriticalPoint_neg_eq_star]
  unfold twistedZetaMomentIntegrand
  let z : ℂ :=
    shortMobiusPolynomial T ((1 / 2 : ℂ) + (t : ℂ) * I) *
      riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)
  change ((‖z‖ ^ 4 : ℝ) : ℂ) = _
  calc
    ((‖z‖ ^ 4 : ℝ) : ℂ) = (((‖z‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
      push_cast
      ring
    _ = (z * star z) ^ 2 := by
      have hnorm : (((‖z‖ ^ 2 : ℝ) : ℂ)) = z * star z := by
        rw [← Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_conj_mul_self]
        exact mul_comm _ _
      rw [hnorm]
    _ = _ := by
      dsimp [z]
      rw [map_mul]
      unfold afeCriticalPoint
      ring

/-- Finite-height Hughes--Young approximation after inserting the actual
squared Maynard--Pratt mollifier on both conjugate critical lines. -/
noncomputable def hughesYoungFiniteTwistedIntegrand
    (T t c H : ℝ) : ℂ :=
  shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
    shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
    hughesYoungFiniteZetaProduct t c H

/-- The finite-height arithmetic approximation converges pointwise to the
actual fourth-power integrand. -/
theorem tendsto_hughesYoungFiniteTwistedIntegrand
    (T t : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (hughesYoungFiniteTwistedIntegrand T t c) atTop
      (𝓝 (twistedZetaMomentIntegrand T t : ℂ)) := by
  have h := (tendsto_hughesYoungFiniteZetaProduct t hc).const_mul
    (shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
      shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2)
  rw [show hughesYoungFiniteTwistedIntegrand T t c = fun H : ℝ =>
      (shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
        shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2) *
          hughesYoungFiniteZetaProduct t c H by
    rfl]
  convert h using 1
  rw [ofReal_twistedZetaMomentIntegrand_eq_conjugate_product]
  ring

/-- One literal `h,k,m,n` term of the finite-height Hughes--Young expansion;
the divisor pair `p=(m,n)` remains countably summed while the two mollifier
indices are finite. -/
noncomputable def hughesYoungFiniteArithmeticTerm
    (T t c H : ℝ) (h k : ℕ) (p : ℕ × ℕ) : ℂ :=
  shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
    shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
    ((1 / (Real.pi : ℂ)) *
      ∫ u in -H..H, hughesYoungRightPairTerm t c u p)

/-!
## The literal Hughes--Young source weight

For fixed mollifier indices `h,k`, Hughes--Young apply DFI to a function of
the physical variables `x = h*m` and `y = k*n`.  Defining that function on
real variables first avoids treating the relation `h*m-k*n=r` as metadata:
the relation is exactly the integer shift seen by `dfiDyadicShiftedDivisorSum`.
-/

/-- The finite-Mellin-height source weight before integrating in the height
variable `t`.  At `(x,y)=(h*m,k*n)` it is precisely the non-divisor part of
`hughesYoungFiniteArithmeticTerm`. -/
noncomputable def hughesYoungFiniteSourceWeight
    (T t c H : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
    shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
    ((1 / (Real.pi : ℂ)) *
      ∫ u in -H..H,
        let w : ℂ := (c : ℂ) + (u : ℂ) * I
        hughesYoungRightContourWeight t c u *
          ((x / (h : ℝ) : ℝ) : ℂ) ^ (-(afeCriticalPoint t + w)) *
          ((y / (k : ℝ) : ℝ) : ℂ) ^ (-(afeCriticalPoint (-t) + w)))

/-- Evaluation of the physical source weight at `(h*m,k*n)` recovers the
exact four-index arithmetic term, with the two divisor coefficients exposed.
This is the source-entry equality needed before splitting by `h*m-k*n`. -/
theorem hughesYoungFiniteArithmeticTerm_eq_divisorWeight_mul_source
    (T t c H : ℝ) {h k m n : ℕ}
    (hh : 0 < h) (hk : 0 < k) :
    hughesYoungFiniteArithmeticTerm T t c H h k (m, n) =
      divisorWeight m * divisorWeight n *
        hughesYoungFiniteSourceWeight T t c H h k
          ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ) := by
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hxm : (((h * m : ℕ) : ℝ) / (h : ℝ)) = (m : ℝ) := by
    push_cast
    field_simp
  have hyn : (((k * n : ℕ) : ℝ) / (k : ℝ)) = (n : ℝ) := by
    push_cast
    field_simp
  unfold hughesYoungFiniteArithmeticTerm hughesYoungRightPairTerm
  simp_rw [divisorDirichletTerm_eq_divisorWeight_mul_cpow]
  unfold hughesYoungFiniteSourceWeight
  simp only [hxm, hyn]
  rw [show (fun u : ℝ =>
      let w : ℂ := (c : ℂ) + (u : ℂ) * I
      hughesYoungRightContourWeight t c u *
          (divisorWeight m * (m : ℂ) ^ (-(afeCriticalPoint t + w))) *
        (divisorWeight n *
          (n : ℂ) ^ (-(afeCriticalPoint (-t) + w)))) =
      fun u : ℝ => divisorWeight m * divisorWeight n *
        (let w : ℂ := (c : ℂ) + (u : ℂ) * I
         hughesYoungRightContourWeight t c u *
            (m : ℂ) ^ (-(afeCriticalPoint t + w)) *
            (n : ℂ) ^ (-(afeCriticalPoint (-t) + w))) by
    funext u
    dsimp only
    ring]
  rw [intervalIntegral.integral_const_mul]
  simp only [Complex.ofReal_natCast, mul_comm]
  ring

/-- Hughes--Young's source weight after the smooth height average.  This is
the function to which the DFI equation-(2) estimates are applied after a
dyadic localization in `x` and `y`. -/
noncomputable def hughesYoungIntegratedSourceWeight
    (T c H : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungFiniteSourceWeight T t c H h k x y

/-- Integrating one four-index term against the authoritative height cutoff
produces the integrated DFI source weight, without changing either divisor
coefficient. -/
theorem integral_hughesYoungFiniteArithmeticTerm_eq_source
    (T c H : ℝ) {h k m n : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t c H h k (m, n) =
      divisorWeight m * divisorWeight n *
        hughesYoungIntegratedSourceWeight T c H h k
          ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ) := by
  rw [show (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFiniteArithmeticTerm T t c H h k (m, n)) =
      fun t : ℝ => divisorWeight m * divisorWeight n *
        ((hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteSourceWeight T t c H h k
            ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ)) by
    funext t
    rw [hughesYoungFiniteArithmeticTerm_eq_divisorWeight_mul_source
      T t c H hh hk]
    ring]
  rw [integral_const_mul]
  rfl

/-- The natural-valued finite shifted sum and the real-physical DFI source
sum agree after the canonical coercion of the physical variables. -/
theorem finiteQuadraticDivisorSum_ofReal_eq_dfiDyadic
    (F : ℝ → ℝ → ℂ) (a b M N : ℕ) (r : ℤ) :
    finiteQuadraticDivisorSum a b M N r
        (fun x y => F (x : ℝ) (y : ℝ)) =
      dfiDyadicShiftedDivisorSum F a b M N r := by
  unfold finiteQuadraticDivisorSum dfiDyadicShiftedDivisorSum
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  push_cast
  rfl

/-- A finite rectangular truncation of the height-integrated off-diagonal
Hughes--Young expansion.  The definition still uses the actual four-index
AFE term; no DFI object occurs in it. -/
noncomputable def hughesYoungFiniteOffDiagonalBox
    (T c H : ℝ) (h k M N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
    if quadraticDivisorShift h k m n = 0 then 0 else
      ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t c H h k (m, n)

/-- Exact Hughes--Young-to-DFI shift partition on one finite rectangle.  In
particular, every nonzero summand is routed by the literal shift `h*m-k*n`,
and the resulting inner sum is exactly `dfiDyadicShiftedDivisorSum`. -/
theorem hughesYoungFiniteOffDiagonalBox_eq_sum_dfiShifts
    (T c H : ℝ) {h k M N : ℕ} (hh : 0 < h) (hk : 0 < k) :
    hughesYoungFiniteOffDiagonalBox T c H h k M N =
      ∑ r ∈ Finset.Icc (-(k * N : ℤ)) (h * M : ℤ),
        if r = 0 then 0 else
          dfiDyadicShiftedDivisorSum
            (hughesYoungIntegratedSourceWeight T c H h k)
            h k M N r := by
  let F : ℝ → ℝ → ℂ := hughesYoungIntegratedSourceWeight T c H h k
  calc
    hughesYoungFiniteOffDiagonalBox T c H h k M N =
        finiteQuadraticDivisorOffDiagonal h k M N
          (fun x y => F (x : ℝ) (y : ℝ)) := by
      unfold hughesYoungFiniteOffDiagonalBox
      apply Finset.sum_congr rfl
      intro m _hm
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hshift : quadraticDivisorShift h k m n = 0
      · simp [hshift]
      · simp only [hshift, if_false]
        rw [integral_hughesYoungFiniteArithmeticTerm_eq_source
          T c H hh hk]
    _ = ∑ r ∈ Finset.Icc (-(k * N : ℤ)) (h * M : ℤ),
        if r = 0 then 0 else
          finiteQuadraticDivisorSum h k M N r
            (fun x y => F (x : ℝ) (y : ℝ)) :=
      finiteQuadraticDivisorOffDiagonal_eq_sum_shifts h k M N _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0
      · simp [hr0]
      · simp only [hr0, if_false]
        exact finiteQuadraticDivisorSum_ofReal_eq_dfiDyadic
          F h k M N r

/-- Exact four-index opening of the finite-height twisted AFE.  This is the
arithmetic source object whose diagonal is `h*m = k*n` and whose nonzero
shift is passed to DFI. -/
theorem hughesYoungFiniteTwistedIntegrand_eq_four_index_sum
    (T t c H : ℝ) :
    hughesYoungFiniteTwistedIntegrand T t c H =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑' p : ℕ × ℕ,
            hughesYoungFiniteArithmeticTerm T t c H h k p := by
  rw [hughesYoungFiniteTwistedIntegrand,
    shortMobiusPolynomial_sq_eq,
    shortMobiusPolynomial_sq_eq]
  unfold hughesYoungFiniteZetaProduct
  rw [mul_assoc, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  calc
    shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
        (shortMobiusSquareCoeff T k *
          (k : ℂ) ^ (-afeCriticalPoint (-t)) *
          ((1 / (Real.pi : ℂ)) *
            ∑' p : ℕ × ℕ,
              ∫ u in -H..H, hughesYoungRightPairTerm t c u p)) =
      shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
        (shortMobiusSquareCoeff T k *
          (k : ℂ) ^ (-afeCriticalPoint (-t)) *
          (∑' p : ℕ × ℕ,
            (1 / (Real.pi : ℂ)) *
              ∫ u in -H..H, hughesYoungRightPairTerm t c u p)) := by
        rw [tsum_mul_left]
    _ =
      shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
        (∑' p : ℕ × ℕ,
          shortMobiusSquareCoeff T k *
            (k : ℂ) ^ (-afeCriticalPoint (-t)) *
            ((1 / (Real.pi : ℂ)) *
              ∫ u in -H..H, hughesYoungRightPairTerm t c u p)) := by
        exact congrArg
          (fun z : ℂ =>
            shortMobiusSquareCoeff T h *
              (h : ℂ) ^ (-afeCriticalPoint t) * z)
          (tsum_mul_left (a :=
            shortMobiusSquareCoeff T k *
              (k : ℂ) ^ (-afeCriticalPoint (-t)))
            (f := fun p : ℕ × ℕ =>
              (1 / (Real.pi : ℂ)) *
                ∫ u in -H..H,
                  hughesYoungRightPairTerm t c u p)).symm
    _ =
      ∑' p : ℕ × ℕ,
        shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
          (shortMobiusSquareCoeff T k *
            (k : ℂ) ^ (-afeCriticalPoint (-t)) *
            ((1 / (Real.pi : ℂ)) *
              ∫ u in -H..H, hughesYoungRightPairTerm t c u p)) := by
        exact tsum_mul_left.symm
    _ = ∑' p : ℕ × ℕ,
        hughesYoungFiniteArithmeticTerm T t c H h k p := by
      apply tsum_congr
      intro p
      unfold hughesYoungFiniteArithmeticTerm
      ring

end RiemannZeta.GuthMaynard

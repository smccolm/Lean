import RiemannZeta.GuthMaynard.HughesYoungActiveComplementContourLimit

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative tail of the Hughes--Young active complement

After the lower dyadic boundary has been removed, the complementary
multiplier vanishes throughout the retained conductor product range.  The
first lemma below converts that exact support statement into the power
majorant used when the signed central source is moved to the opening line.
-/

/-- The lower-boundary-removed complement is bounded by any positive power
of the ratio between the physical product and the retained conductor
product.  The one-extra-step cover is exactly the hypothesis under which
the complement vanishes on the retained range. -/
theorem hughesYoungNonLowerActiveComplementMultiplier_le_productRatio_rpow
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    {x y η : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hη : 0 ≤ η)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    hughesYoungNonLowerActiveComplementMultiplier a b R K x y ≤
      (x * y / ((a * b * R : ℕ) : ℝ)) ^ η := by
  let A : ℝ := ((a * b * R : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  by_cases hm :
      hughesYoungNonLowerActiveComplementMultiplier a b R K x y = 0
  · rw [hm]
    exact Real.rpow_nonneg (div_nonneg (mul_nonneg hx hy) hA.le) η
  · have hprod : A < x * y := by
      by_contra hnot
      apply hm
      exact
        hughesYoungNonLowerActiveComplementMultiplier_eq_zero_of_product_le_of_strongCover
          hx hy hstrong (le_of_not_gt hnot)
    have hratio : 1 ≤ x * y / A := by
      apply (le_div_iff₀ hA).2
      simpa using hprod.le
    calc
      hughesYoungNonLowerActiveComplementMultiplier a b R K x y ≤ 1 :=
        hughesYoungNonLowerActiveComplementMultiplier_le_one a b R K hx hy
      _ ≤ (x * y / A) ^ η := Real.one_le_rpow hratio hη
      _ = (x * y / ((a * b * R : ℕ) : ℝ)) ^ η := rfl

/-- Moving the real part of the affine-beta exponent to the left is
exactly multiplication by the corresponding positive product power. -/
theorem rpow_mul_norm_hughesYoungCriticalAffineBetaIntegrand_eq_shift
    (t u c η : ℝ) {x : ℝ} (hx : 0 < x) (CX COne : ℂ) :
    (x * (1 + x)) ^ η *
        ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ =
      ‖hughesYoungCriticalAffineBetaIntegrand t u (c - η) x CX COne‖ := by
  have hone : 0 < 1 + x := by linarith
  have hxpow :
      x ^ η * x ^ (-(1 / 2 : ℝ) - c) =
        x ^ (-(1 / 2 : ℝ) - (c - η)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have honepow :
      (1 + x) ^ η * (1 + x) ^ (-(1 / 2 : ℝ) - c) =
        (1 + x) ^ (-(1 / 2 : ℝ) - (c - η)) := by
    rw [← Real.rpow_add hone]
    congr 1
    ring
  have hnorm (d : ℝ) :
      ‖hughesYoungCriticalAffineBetaIntegrand t u d x CX COne‖ =
        ‖(Real.log x : ℂ) + CX‖ *
          ‖(Real.log (1 + x) : ℂ) + COne‖ *
          (x ^ (-(1 / 2 : ℝ) - d) *
            (1 + x) ^ (-(1 / 2 : ℝ) - d)) := by
    unfold hughesYoungCriticalAffineBetaIntegrand
    dsimp only
    rw [norm_mul, norm_mul,
      norm_hughesYoungCriticalAffineBetaPower_eq (t := t) (u := u)
        (c := d) hx]
  rw [hnorm c, hnorm (c - η), Real.mul_rpow hx.le hone.le]
  rw [show x ^ η * (1 + x) ^ η *
      (‖(Real.log x : ℂ) + CX‖ * ‖(Real.log (1 + x) : ℂ) + COne‖ *
        (x ^ (-(1 / 2 : ℝ) - c) *
          (1 + x) ^ (-(1 / 2 : ℝ) - c))) =
      (‖(Real.log x : ℂ) + CX‖ * ‖(Real.log (1 + x) : ℂ) + COne‖) *
        ((x ^ η * x ^ (-(1 / 2 : ℝ) - c)) *
          ((1 + x) ^ η * (1 + x) ^ (-(1 / 2 : ℝ) - c))) by ring,
    hxpow, honepow]

/-- The same contour-line shift after the exact DFI positive-shift
dilation.  The physical product is `(r*x+r)*(r*x)`, so the two dilation
powers and the affine-beta kernel move together. -/
theorem rpow_mul_norm_hughesYoungDilatedCriticalAffineBeta_eq_shift
    (t u c η : ℝ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x)
    (CX COne : ℂ) :
    ((r * x + r) * (r * x)) ^ η *
        ‖(r : ℂ) ^ (-(afeCriticalPoint t +
              ((c : ℂ) + (u : ℂ) * I))) *
            (r : ℂ) ^ (-(afeCriticalPoint (-t) +
              ((c : ℂ) + (u : ℂ) * I))) *
            hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ =
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            (r : ℂ) ^ (-(afeCriticalPoint (-t) +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            hughesYoungCriticalAffineBetaIntegrand
              t u (c - η) x CX COne‖ := by
  have hone : 0 < 1 + x := by linarith
  have hprod : (r * x + r) * (r * x) = r ^ 2 * (x * (1 + x)) := by ring
  have hdpow :
      r ^ (2 * η) * r ^ (-(1 + 2 * c : ℝ)) =
        r ^ (-(1 + 2 * (c - η) : ℝ)) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hbeta :=
    rpow_mul_norm_hughesYoungCriticalAffineBetaIntegrand_eq_shift
      t u c η hx CX COne
  rw [hprod, Real.mul_rpow (sq_nonneg r) (mul_nonneg hx.le hone.le)]
  rw [show r ^ 2 = r ^ (2 : ℝ) by rw [Real.rpow_two],
    ← Real.rpow_mul hr.le]
  repeat' rw [norm_mul]
  rw [show ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I)))‖ =
      r ^ (-(1 + 2 * c : ℝ)) by
        simpa only [norm_mul] using
          norm_hughesYoungDilationPowerPair_horizontal t c u hr,
    show ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          (((c - η : ℝ) : ℂ) + (u : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          (((c - η : ℝ) : ℂ) + (u : ℂ) * I)))‖ =
      r ^ (-(1 + 2 * (c - η) : ℝ)) by
        simpa only [norm_mul] using
          norm_hughesYoungDilationPowerPair_horizontal t (c - η) u hr]
  calc
    r ^ (2 * η) * (x * (1 + x)) ^ η *
          (r ^ (-(1 + 2 * c : ℝ)) *
            ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖) =
        (r ^ (2 * η) * r ^ (-(1 + 2 * c : ℝ))) *
          ((x * (1 + x)) ^ η *
            ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖) := by ring
    _ = r ^ (-(1 + 2 * (c - η) : ℝ)) *
          ‖hughesYoungCriticalAffineBetaIntegrand
            t u (c - η) x CX COne‖ := by rw [hdpow, hbeta]

/-- Uniform affine-beta domination on an arbitrary compact positive strip.
The existing integrable `Re w = c₀` majorant is reused after shifting the
real exponent back to `c₀`; the positive physical cutoff controls the
resulting negative product power. -/
theorem norm_hughesYoungCriticalAffineBetaIntegrand_le_arbitraryStripMajorant
    {t u c₀ c₁ c δ x : ℝ} {CX COne : ℂ}
    (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    (hc : c ∈ Set.Icc c₀ c₁) (hδ : 0 < δ) (hxδ : δ < x) :
    ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
      max 1 ((δ * (1 + δ)) ^ (-(c₁ - c₀))) *
        hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ
          (1 + ‖CX‖ + ‖COne‖) x := by
  let p : ℝ := x * (1 + x)
  let p₀ : ℝ := δ * (1 + δ)
  let η : ℝ := c - c₀
  let D : ℝ := c₁ - c₀
  have hx : 0 < x := hδ.trans hxδ
  have hp : 0 < p := by dsimp only [p]; positivity
  have hp₀ : 0 < p₀ := by dsimp only [p₀]; positivity
  have hp₀p : p₀ ≤ p := by
    dsimp only [p₀, p]
    nlinarith
  have hη : 0 ≤ η := by dsimp only [η]; linarith [hc.1]
  have hηD : η ≤ D := by dsimp only [η, D]; linarith [hc.2]
  have hD : 0 ≤ D := hη.trans hηD
  have hshift :=
    rpow_mul_norm_hughesYoungCriticalAffineBetaIntegrand_eq_shift
      t u c η hx CX COne
  have hcshift : c - η = c₀ := by dsimp only [η]; ring
  rw [hcshift] at hshift
  have heq :
      ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ =
        p ^ (-η) *
          ‖hughesYoungCriticalAffineBetaIntegrand t u c₀ x CX COne‖ := by
    have hpow : p ^ (-η) * p ^ η = 1 := by
      rw [← Real.rpow_add hp]
      simp
    dsimp only [p] at hshift ⊢
    calc
      _ = 1 * ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ := by rw [one_mul]
      _ = (p ^ (-η) * p ^ η) *
          ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ := by rw [hpow]
      _ = p ^ (-η) *
          (p ^ η * ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖) := by ring
      _ = _ := by rw [hshift]
  have hpowBound : p ^ (-η) ≤ max 1 (p₀ ^ (-D)) := by
    by_cases hpOne : 1 ≤ p
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hpOne (neg_nonpos.mpr hη)).trans
        (le_max_left _ _)
    · have hpLe : p ≤ 1 := le_of_not_ge hpOne
      have hexp : -D ≤ -η := by linarith
      have hfirst : p ^ (-η) ≤ p ^ (-D) :=
        Real.rpow_le_rpow_of_exponent_ge hp hpLe hexp
      have hsecond : p ^ (-D) ≤ p₀ ^ (-D) :=
        Real.rpow_le_rpow_of_nonpos hp₀ hp₀p (neg_nonpos.mpr hD)
      exact (hfirst.trans hsecond).trans (le_max_right _ _)
  have hbase :=
    norm_hughesYoungCriticalAffineBetaIntegrand_le_fullStripMajorant
      hc₀ le_rfl hc₀one hδ hxδ
      (t := t) (u := u) (CX := CX) (COne := COne)
  rw [heq]
  calc
    p ^ (-η) *
          ‖hughesYoungCriticalAffineBetaIntegrand t u c₀ x CX COne‖ ≤
        max 1 (p₀ ^ (-D)) *
          ‖hughesYoungCriticalAffineBetaIntegrand t u c₀ x CX COne‖ :=
      mul_le_mul_of_nonneg_right hpowBound (norm_nonneg _)
    _ ≤ max 1 (p₀ ^ (-D)) *
        hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ
          (1 + ‖CX‖ + ‖COne‖) x :=
      mul_le_mul_of_nonneg_left hbase (zero_le_one.trans (le_max_left _ _))

/-- Height-uniform DFI-dilate estimate on an arbitrary compact positive
Mellin strip.  This removes the artificial `c₁ ≤ 1` restriction from the
contour-exhaustion argument while retaining the same integrable physical
majorant and Gaussian decay in the horizontal height. -/
theorem exists_norm_scalar_nonLowerActiveComplement_horizontal_dilate_le_arbitraryStripGaussianMajorant
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t : ℝ) {h k : ℕ}
    (a b R K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 1 ≤ |H| →
      ∀ (qx qy : ℕ) (c : ℝ), c ∈ Set.Icc c₀ c₁ →
      ∀ x : ℝ, (1 / hughesYoungDyadicRatio) / r < x →
        ‖dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
          (r * x + r) (r * x)‖ ≤
        D * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
            (2 + |t| + c₁ + |H|) ^ 16) *
          hughesYoungCriticalAffineBetaFullStripMajorant c₀
            ((1 / hughesYoungDyadicRatio) / r)
            (1 +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  let Cshift : ℝ := max 1 ((δ * (1 + δ)) ^ (-(c₁ - c₀)))
  obtain ⟨Cr, hCr, hrpow⟩ :=
    exists_uniform_norm_hughesYoungDilationPowerPair_all_horizontal
      t hr c₀ c₁
  obtain ⟨Cs, hCs, hscale⟩ :=
    exists_norm_hughesYoungReducedMellinScaleConstantComplex_horizontal_le_gaussian_abs
      T t h k hc₀ hc
  let D₀ : ℝ := ‖z‖ * Cs * Cr * Cshift
  let D : ℝ := max 1 D₀
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro H hH qx qy c hcMem x hx
  let CX : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  let G : ℝ := hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ
    (1 + ‖CX‖ + ‖COne‖) x
  have hδ : 0 < δ := div_pos
    (one_div_pos.mpr hughesYoungDyadicRatio_pos) hr
  have hx₀ : 0 < x := hδ.trans hx
  have hrx : 0 ≤ r * x := (mul_pos hr hx₀).le
  have hrOne : 0 ≤ r * x + r := (add_pos (mul_pos hr hx₀) hr).le
  have hmult := hughesYoungNonLowerActiveComplementMultiplier_le_one
    a b R K hrOne hrx
  have hmult₀ := hughesYoungNonLowerActiveComplementMultiplier_nonneg
    a b R K hrOne hrx
  have hbeta :
      ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ ≤
        Cshift * G := by
    exact norm_hughesYoungCriticalAffineBetaIntegrand_le_arbitraryStripMajorant
      hc₀ hc₀one hcMem hδ hx
  have hshape :=
    dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c H a b qx qy R K hr hx₀
  have hscale' := hscale H hH c hcMem
  have hrpow' := hrpow H c hcMem
  rw [show dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x) =
      z *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (H : ℂ) * I) a b R K)
          (r * x + r) (r * x) by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring]
  rw [hshape]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmult₀]
  have hbeta₀ : 0 ≤ ‖hughesYoungCriticalAffineBetaIntegrand
      t H c x CX COne‖ := norm_nonneg _
  have hmultBeta :
      hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ ≤
        Cshift * G := by
    calc
      _ ≤ 1 * ‖hughesYoungCriticalAffineBetaIntegrand
          t H c x CX COne‖ :=
        mul_le_mul_of_nonneg_right hmult hbeta₀
      _ = ‖hughesYoungCriticalAffineBetaIntegrand
          t H c x CX COne‖ := one_mul _
      _ ≤ Cshift * G := hbeta
  have hrpowNorm :
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (H : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (H : ℂ) * I)))‖ ≤ Cr := by
    simpa only [norm_mul] using hrpow'
  have hG₀ : 0 ≤ G := hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
  have hE₀ : 0 ≤ E := by dsimp only [E]; positivity
  have hCshift₀ : 0 ≤ Cshift := by dsimp only [Cshift]; positivity
  have hscaleE :
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        ((c : ℂ) + (H : ℂ) * I) h k‖ ≤ Cs * E := by
    simpa only [E, mul_assoc] using hscale'
  calc
    _ = ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k‖ *
        (‖(r : ℂ) ^ (-(afeCriticalPoint t +
            ((c : ℂ) + (H : ℂ) * I)))‖ *
          ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
            ((c : ℂ) + (H : ℂ) * I)))‖) *
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖) := by
      dsimp only [CX, COne]
      ring
    _ ≤ ‖z‖ * (Cs * E) * Cr * (Cshift * G) := by gcongr
    _ = D₀ * E * G := by dsimp only [D₀]; ring
    _ ≤ D * E * G := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 1 D₀) hE₀) hG₀
    _ = _ := rfl

/-- Uniform inverse-square/log-square summand bound on an arbitrary compact
positive strip, with a constant selected before the horizontal height. -/
theorem exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le_arbitraryStripGaussian
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (R K : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ H : ℝ, 1 ≤ |H| → ∀ (q : ℕ) (c : ℝ),
      c ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r q‖ ≤
      B * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + |H|) ^ 16) *
        (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨D, hD, hsource⟩ :=
    exists_norm_scalar_nonLowerActiveComplement_horizontal_dilate_le_arbitraryStripGaussianMajorant
      hc₀ hc hc₀one z t a b R K hrR (T := T) (h := h) (k := k)
  let delta : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
  let Ddelta : ℝ := max 1 (delta ^ (-(3 / 4 : ℝ)))
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let B : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * (r : ℝ) * D *
      (2312 * Ddelta + 9 * c₀⁻¹ ^ 3)
  have hB : 0 < B := by
    dsimp only [B]
    have habC : ((a : ℂ) * b) ≠ 0 := by
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb))
    have habr : 0 < ((a * b * r ^ 2 : ℕ) : ℝ) := by positivity
    have hnorm : 0 < ‖((a : ℂ) * b)⁻¹‖ :=
      norm_pos_iff.mpr (inv_ne_zero habC)
    have hlast : 0 < 2312 * Ddelta + 9 * c₀⁻¹ ^ 3 := by
      have hDdelta : 0 < Ddelta :=
        lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      positivity
    exact mul_pos (mul_pos (mul_pos (mul_pos hnorm habr) hrR) hD) hlast
  refine ⟨B, hB, ?_⟩
  intro H hH q c hcMem
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  have hE₀ : 0 ≤ E := by dsimp only [E]; positivity
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    let qx : ℕ := dfiReducedDenominator a q
    let qy : ℕ := dfiReducedDenominator b q
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
    let F : ℝ → ℂ := fun x =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        ((r : ℝ) * x + r) ((r : ℝ) * x)
    let J : ℝ → ℂ := fun x => (Set.Ioi delta).indicator F x
    have hdelta : 0 < delta := div_pos
      (one_div_pos.mpr hughesYoungDyadicRatio_pos) hrR
    have hGint : Integrable
        (hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S) :=
      integrable_hughesYoungCriticalAffineBetaFullStripMajorant hc₀
    have hDEGint : Integrable (fun x : ℝ =>
        (D * E) * hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x) :=
      hGint.const_mul (D * E)
    have hJbound (x : ℝ) :
        ‖J x‖ ≤ (D * E) *
          hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := by
      by_cases hxmem : x ∈ Set.Ioi delta
      · have hJ : J x = F x := by simp [J, hxmem]
        rw [hJ]
        simpa only [E, mul_assoc] using hsource H hH qx qy c hcMem x hxmem
      · have hJ : J x = 0 := by simp [J, hxmem]
        rw [hJ, norm_zero]
        exact mul_nonneg (mul_nonneg hD.le hE₀)
          hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    have hIntRaw := MeasureTheory.norm_integral_le_of_norm_le hDEGint
      (Filter.Eventually.of_forall hJbound)
    have hInt :
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ ≤
          (D * E) * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3) := by
      calc
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ = ‖∫ x : ℝ, J x‖ := by
          simp only [J, MeasureTheory.integral_indicator measurableSet_Ioi]
        _ ≤ ∫ x : ℝ, (D * E) *
            hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := hIntRaw
        _ = (D * E) * ∫ x : ℝ,
            hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := by
          rw [MeasureTheory.integral_const_mul]
        _ = (D * E) *
            (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3) := by
          rw [integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq hc₀]
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A, qx, qy]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS₀ : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile₀ : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCentral :=
      dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
        T t ((c : ℂ) + (H : ℂ) * I) z h k a b qx qy R K hrR
    unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      dfiEquation27CentralSummand
    rw [hCentral]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrR]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((r : ℝ) * ‖∫ x : ℝ in Set.Ioi delta, F x‖) ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) * ((D * E) *
            (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3))) := by
        gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) * ((D * E) *
            ((2312 * Ddelta + 9 * c₀⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3 =
              (2312 * Ddelta + 9 * c₀⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 * Ddelta + 9 * c₀⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = B * E * (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [B, A]
        ac_rfl

set_option maxHeartbeats 1600000 in
/-- Joint absolute integrability on a horizontal edge of an arbitrary
positive rectangle.  The hypothesis `1 ≤ |H|` is exactly the range used in
the contour-exhaustion limit. -/
theorem integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t H : ℝ) (hH : 1 ≤ |H|)
    {h k : ℕ} (a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2))
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi
          ((1 / hughesYoungDyadicRatio) / r)))) := by
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  have hδ : 0 < δ := div_pos
    (one_div_pos.mpr hughesYoungDyadicRatio_pos) hr
  obtain ⟨D, hD, hsource⟩ :=
    exists_norm_scalar_nonLowerActiveComplement_horizontal_dilate_le_arbitraryStripGaussianMajorant
      hc₀ hc hc₀one z t a b R K hr (T := T) (h := h) (k := k)
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  let G : ℝ → ℝ := fun x =>
    hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ
      (1 +
        ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
        ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x
  have hE₀ : 0 ≤ E := by dsimp only [E]; positivity
  have hG : Integrable G := by
    simpa only [G] using
      (integrable_hughesYoungCriticalAffineBetaFullStripMajorant
        (c₀ := c₀) (δ := δ)
        (S := 1 +
          ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
          ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) hc₀)
  have hconst : Integrable (fun _ : ℝ => D * E)
      (volume.restrict (Set.Icc c₀ c₁)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hmajor : Integrable (fun p : ℝ × ℝ => (D * E) * G p.2)
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi δ))) := by
    have hDE₀ : 0 ≤ D * E := mul_nonneg hD.le hE₀
    have hGon : Integrable G (volume.restrict (Set.Ioi δ)) :=
      hG.integrableOn
    simpa [Real.norm_eq_abs, abs_of_nonneg hDE₀,
      abs_of_nonneg hD.le, abs_of_nonneg hE₀] using
      hconst.norm.mul_prod hGon
  let F : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let CX : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  let Qf : ℝ × ℝ → ℂ := fun p =>
    z *
      hughesYoungReducedMellinScaleConstantComplex T t
        ((p.1 : ℂ) + (H : ℂ) * I) h k *
      (hughesYoungNonLowerActiveComplementMultiplier
        a b R K (r * p.2 + r) (r * p.2) : ℂ) *
      (r : ℂ) ^ (-(afeCriticalPoint t +
        ((p.1 : ℂ) + (H : ℂ) * I))) *
      (r : ℂ) ^ (-(afeCriticalPoint (-t) +
        ((p.1 : ℂ) + (H : ℂ) * I))) *
      hughesYoungCriticalAffineBetaIntegrand t H p.1 p.2 CX COne
  have hQcont : ContinuousOn Qf (Set.Icc c₀ c₁ ×ˢ Set.Ioi δ) := by
    intro p hp
    have hcPos : 0 < p.1 := hc₀.trans_le hp.1.1
    have hx₀ : 0 < p.2 := hδ.trans hp.2
    have hrBase : (r : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hr
    have hxBase : (p.2 : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hx₀
    have hOneBase : 1 + (p.2 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using (show 0 < 1 + p.2 by linarith)
    have hscaleAt : ContinuousAt (fun q : ℝ × ℝ =>
        hughesYoungReducedMellinScaleConstantComplex T t
          ((q.1 : ℂ) + (H : ℂ) * I) h k) p :=
      (differentiableAt_hughesYoungReducedMellinScaleConstantComplex
        T t h k (by simpa using hcPos)).continuousAt.comp (by fun_prop)
    have hmultAt : ContinuousAt (fun q : ℝ × ℝ =>
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * q.2 + r) (r * q.2) : ℂ)) p := by
      apply (Complex.continuous_ofReal.comp ?_).continuousAt
      unfold hughesYoungNonLowerActiveComplementMultiplier
        hughesYoungActiveContinuousDyadicWeight hughesYoungFullDyadicCutoff
      apply Continuous.sub
      · exact (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop))).mul
          (continuous_const.sub
            (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)))
      · apply continuous_finsetSum
        intro ij _hij
        exact ((contDiff_hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale ij.1)).continuous.comp
              (by fun_prop)).mul
          ((contDiff_hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale ij.2)).continuous.comp
              (by fun_prop))
    have hrpow₁ : ContinuousAt (fun q : ℝ × ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint t +
          ((q.1 : ℂ) + (H : ℂ) * I)))) p :=
      continuousAt_const.cpow (by fun_prop) hrBase
    have hrpow₂ : ContinuousAt (fun q : ℝ × ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((q.1 : ℂ) + (H : ℂ) * I)))) p :=
      continuousAt_const.cpow (by fun_prop) hrBase
    have hlogX : ContinuousAt (fun q : ℝ × ℝ =>
        (Real.log q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_log (ne_of_gt hx₀)).comp continuousAt_snd)
    have hlogOne : ContinuousAt (fun q : ℝ × ℝ =>
        (Real.log (1 + q.2) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        (((Real.continuousAt_log (by linarith : 1 + p.2 ≠ 0)).comp
          (continuousAt_const.add continuousAt_id)).comp continuousAt_snd)
    have hbaseX : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    have hbaseOne : ContinuousAt (fun q : ℝ × ℝ =>
        1 + (q.2 : ℂ)) p := continuousAt_const.add hbaseX
    have hexpX : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint (-t) + ((q.1 : ℂ) + (H : ℂ) * I))) p := by
      fun_prop
    have hexpOne : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint t + ((q.1 : ℂ) + (H : ℂ) * I))) p := by
      fun_prop
    have hbetaAt : ContinuousAt (fun q : ℝ × ℝ =>
        hughesYoungCriticalAffineBetaIntegrand t H q.1 q.2 CX COne) p := by
      unfold hughesYoungCriticalAffineBetaIntegrand
      exact (((hlogX.add continuousAt_const).mul
        (hlogOne.add continuousAt_const)).mul
          ((hbaseX.cpow hexpX hxBase).mul
            (hbaseOne.cpow hexpOne hOneBase)))
    dsimp only [Qf]
    exact (((((continuousAt_const.mul hscaleAt).mul hmultAt).mul
      hrpow₁).mul hrpow₂).mul hbetaAt).continuousWithinAt
  have hFQ : Set.EqOn F Qf (Set.Icc c₀ c₁ ×ˢ Set.Ioi δ) := by
    intro p hp
    have hx₀ : 0 < p.2 := hδ.trans hp.2
    dsimp only [F, Qf]
    rw [show dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2) =
        z * hughesYoungReducedMellinScaleConstantComplex T t
          ((p.1 : ℂ) + (H : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((p.1 : ℂ) + (H : ℂ) * I) a b R K)
          (r * p.2 + r) (r * p.2) by
      unfold dfiEquation27C
      dsimp only
      rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
      ring]
    rw [dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t p.1 H a b qx qy R K hr hx₀]
    dsimp only [CX, COne]
    ring
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi δ))) := by
    rw [Measure.prod_restrict]
    exact (hQcont.congr hFQ).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_Ioi)
  change Integrable F
    ((volume.restrict (Set.Icc c₀ c₁)).prod
      (volume.restrict (Set.Ioi δ)))
  apply hmajor.mono' hmeas
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc.prod measurableSet_Ioi)] with p hp
  exact hsource H hH qx qy p.1 hp.1 p.2 hp.2

set_option maxHeartbeats 1000000 in
/-- Joint absolute integrability on one vertical edge of an arbitrary
compact positive Mellin strip after the exact positive-shift DFI dilation.
The physical variable stays away from zero, so shifting the real exponent
back to the fixed base line yields an integrable majorant at every edge. -/
theorem integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint_arbitraryStrip
    {T c₀ c₁ c : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    (hc : c ∈ Set.Icc c₀ c₁)
    (z : ℂ) (t H : ℝ) {h k : ℕ} (a b qx qy R K : ℕ)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2))
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi
          ((1 / hughesYoungDyadicRatio) / r)))) := by
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  have hδ : 0 < δ := div_pos
    (one_div_pos.mpr hughesYoungDyadicRatio_pos) hr
  have hcPos : 0 < c := hc₀.trans_le hc.1
  let Cshift : ℝ := max 1 ((δ * (1 + δ)) ^ (-(c₁ - c₀)))
  let CX : ℂ :=
    (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ :=
    (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  let G : ℝ → ℝ :=
    hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ
      (1 + ‖CX‖ + ‖COne‖)
  have hG : Integrable G := by
    simpa only [G] using
      (integrable_hughesYoungCriticalAffineBetaFullStripMajorant
        (c₀ := c₀) (δ := δ)
        (S := 1 + ‖CX‖ + ‖COne‖) hc₀)
  obtain ⟨Cr, hCr, hrpow⟩ :=
    exists_uniform_norm_hughesYoungDilationPowerPair_vertical
      t c H hr
  obtain ⟨Cs, hCs, hscale⟩ :=
    exists_uniform_norm_hughesYoungReducedMellinScaleConstantComplex_vertical
      T t c H h k hcPos
  let D : ℝ := ‖z‖ * Cs * Cr * Cshift
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hconst : Integrable (fun _ : ℝ => D)
      (volume.restrict (Set.Icc (-H) H)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hGon : Integrable G (volume.restrict (Set.Ioi δ)) :=
    hG.integrableOn
  have hmajor : Integrable (fun p : ℝ × ℝ => D * G p.2)
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi δ))) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hD] using
      hconst.norm.mul_prod hGon
  let F : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Q : ℝ × ℝ → ℂ := fun p =>
    z *
      hughesYoungReducedMellinScaleConstantComplex T t
        ((c : ℂ) + (p.1 : ℂ) * I) h k *
      (hughesYoungNonLowerActiveComplementMultiplier
        a b R K (r * p.2 + r) (r * p.2) : ℂ) *
      (r : ℂ) ^ (-(afeCriticalPoint t +
        ((c : ℂ) + (p.1 : ℂ) * I))) *
      (r : ℂ) ^ (-(afeCriticalPoint (-t) +
        ((c : ℂ) + (p.1 : ℂ) * I))) *
      hughesYoungCriticalAffineBetaIntegrand t p.1 c p.2 CX COne
  have hQcont : ContinuousOn Q
      (Set.Icc (-H) H ×ˢ Set.Ioi δ) := by
    intro p hp
    have hx0 : 0 < p.2 := hδ.trans hp.2
    have hrBase : (r : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hr
    have hxBase : (p.2 : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hx0
    have hOneBase : 1 + (p.2 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using (show 0 < 1 + p.2 by linarith)
    have hline : ContinuousAt
        (fun q : ℝ × ℝ => (c : ℂ) + (q.1 : ℂ) * I) p := by
      fun_prop
    have hdiff :=
      differentiableAt_hughesYoungReducedMellinScaleConstantComplex
        T t h k (w := (c : ℂ) + (p.1 : ℂ) * I)
          (by simpa using hcPos)
    have hscaleAt : ContinuousAt (fun q : ℝ × ℝ =>
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (q.1 : ℂ) * I) h k) p :=
      ContinuousAt.comp
        (g := fun z : ℂ =>
          hughesYoungReducedMellinScaleConstantComplex T t z h k)
        (f := fun q : ℝ × ℝ => (c : ℂ) + (q.1 : ℂ) * I)
        hdiff.continuousAt hline
    have hmultAt : ContinuousAt (fun q : ℝ × ℝ =>
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * q.2 + r) (r * q.2) : ℂ)) p := by
      apply (Complex.continuous_ofReal.comp ?_).continuousAt
      unfold hughesYoungNonLowerActiveComplementMultiplier
        hughesYoungActiveContinuousDyadicWeight
        hughesYoungFullDyadicCutoff
      apply Continuous.sub
      · exact (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop))).mul
          (continuous_const.sub
            (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)))
      · apply continuous_finsetSum
        intro ij _hij
        exact ((contDiff_hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale ij.1)).continuous.comp
              (by fun_prop)).mul
          ((contDiff_hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale ij.2)).continuous.comp
              (by fun_prop))
    have hrpow₁ : ContinuousAt (fun q : ℝ × ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (q.1 : ℂ) * I)))) p :=
      continuousAt_const.cpow (by fun_prop) hrBase
    have hrpow₂ : ContinuousAt (fun q : ℝ × ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (q.1 : ℂ) * I)))) p :=
      continuousAt_const.cpow (by fun_prop) hrBase
    have hlogX : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_log (ne_of_gt hx0)).comp continuousAt_snd)
    have hlogOne : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log (1 + q.2) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        (((Real.continuousAt_log (by linarith : 1 + p.2 ≠ 0)).comp
          (continuousAt_const.add continuousAt_id)).comp continuousAt_snd)
    have hbaseX : ContinuousAt
        (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    have hbaseOne : ContinuousAt
        (fun q : ℝ × ℝ => 1 + (q.2 : ℂ)) p :=
      continuousAt_const.add hbaseX
    have hexpX : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint (-t) +
          ((c : ℂ) + (q.1 : ℂ) * I))) p := by
      fun_prop
    have hexpOne : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint t +
          ((c : ℂ) + (q.1 : ℂ) * I))) p := by
      fun_prop
    have hbetaAt : ContinuousAt (fun q : ℝ × ℝ =>
        hughesYoungCriticalAffineBetaIntegrand
          t q.1 c q.2 CX COne) p := by
      unfold hughesYoungCriticalAffineBetaIntegrand
      exact (((hlogX.add continuousAt_const).mul
        (hlogOne.add continuousAt_const)).mul
          ((hbaseX.cpow hexpX hxBase).mul
            (hbaseOne.cpow hexpOne hOneBase)))
    dsimp only [Q]
    exact (((((continuousAt_const.mul hscaleAt).mul hmultAt).mul
      hrpow₁).mul hrpow₂).mul hbetaAt).continuousWithinAt
  have hFQ : Set.EqOn F Q
      (Set.Icc (-H) H ×ˢ Set.Ioi δ) := by
    intro p hp
    have hx0 : 0 < p.2 := hδ.trans hp.2
    dsimp only [F, Q]
    rw [show dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2) =
        z *
          hughesYoungReducedMellinScaleConstantComplex T t
            ((c : ℂ) + (p.1 : ℂ) * I) h k *
          dfiEquation27C a b qx qy
            (hughesYoungNonLowerActiveComplementMellinShapeComplex
              t ((c : ℂ) + (p.1 : ℂ) * I) a b R K)
            (r * p.2 + r) (r * p.2) by
      unfold dfiEquation27C
      dsimp only
      rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
      ring]
    rw [dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c p.1 a b qx qy R K hr hx0]
    dsimp only [CX, COne]
    ring
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi δ))) := by
    rw [Measure.prod_restrict]
    exact (hQcont.congr hFQ).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_Ioi)
  change Integrable F
    ((volume.restrict (Set.Icc (-H) H)).prod
      (volume.restrict (Set.Ioi δ)))
  apply hmajor.mono' hmeas
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc.prod measurableSet_Ioi)] with p hp
  rcases hp with ⟨hu, hx⟩
  let u := p.1
  let x := p.2
  change ‖dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x)‖ ≤ D * G x
  have hx0 : 0 < x := hδ.trans hx
  have hrx : 0 ≤ r * x := (mul_pos hr hx0).le
  have hrOne : 0 ≤ r * x + r := (add_pos (mul_pos hr hx0) hr).le
  have hmult := hughesYoungNonLowerActiveComplementMultiplier_le_one
    a b R K hrOne hrx
  have hmult0 := hughesYoungNonLowerActiveComplementMultiplier_nonneg
    a b R K hrOne hrx
  have hbeta' :
      ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
        Cshift * G x := by
    simpa only [Cshift, G, CX, COne] using
      (norm_hughesYoungCriticalAffineBetaIntegrand_le_arbitraryStripMajorant
        (t := t) (u := u) (c₀ := c₀) (c₁ := c₁) (c := c)
        (δ := δ) (x := x) (CX := CX) (COne := COne)
        hc₀ hc₀one hc hδ hx)
  have hshape :=
    dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c u a b qx qy R K hr hx0
  have hscale' := hscale u hu
  have hrpow' := hrpow u hu
  rw [show dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x) =
      z *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (u : ℂ) * I) a b R K)
          (r * x + r) (r * x) by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring]
  rw [hshape]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmult0]
  have hbeta0 : 0 ≤
      ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ :=
    norm_nonneg _
  have hmultBeta :
      hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
        Cshift * G x := by
    calc
      _ ≤ 1 * ‖hughesYoungCriticalAffineBetaIntegrand
          t u c x CX COne‖ :=
        mul_le_mul_of_nonneg_right hmult hbeta0
      _ = ‖hughesYoungCriticalAffineBetaIntegrand
          t u c x CX COne‖ := one_mul _
      _ ≤ Cshift * G x := hbeta'
  have hrpowNorm :
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I)))‖ ≤ Cr := by
    simpa only [norm_mul] using hrpow'
  calc
    _ = ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        (‖(r : ℂ) ^ (-(afeCriticalPoint t +
            ((c : ℂ) + (u : ℂ) * I)))‖ *
          ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
            ((c : ℂ) + (u : ℂ) * I)))‖) *
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand
            t u c x CX COne‖) := by
      dsimp only [CX, COne]
      ring
    _ ≤ ‖z‖ * Cs * Cr * (Cshift * G x) := by
      gcongr
    _ = D * G x := by
      dsimp only [D]
      ring

set_option maxHeartbeats 1600000 in
/-- Exact DFI physical-integral rectangle identity on an arbitrary compact
positive Mellin strip.  Both horizontal edges use the Gaussian strip
majorant and both vertical edges use exponent transport to the base line. -/
theorem integral_dfiEquation27C_scalar_mul_nonLowerActiveComplement_dilated_boundaryRect_zero_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t : ℝ) {H : ℝ} (hH : 1 ≤ H)
    (h k a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) -
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((s : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) +
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) -
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) = 0 := by
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  let Fb : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((p.1 : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Ft : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Fr : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c₁ : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Fl : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c₀ : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  change
    (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi δ, Fb (s, x)) -
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi δ, Ft (s, x)) +
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi δ, Fr (u, x)) -
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi δ, Fl (u, x)) = 0
  have hb : Integrable Fb
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi δ))) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((p.1 : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y)
          (r * p.2 + r) (r * p.2))
        ((volume.restrict (Set.Icc c₀ c₁)).prod
          (volume.restrict (Set.Ioi ((1 / hughesYoungDyadicRatio) / r))))
    have hraw :=
      integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint_arbitraryStrip
        hc₀ hc hc₀one z t (-H)
          (by simpa [abs_of_nonneg (zero_le_one.trans hH)] using hH)
          a b qx qy R K hr (T := T) (h := h) (k := k)
    refine hraw.congr ?_
    filter_upwards [] with p
    rfl
  have ht : Integrable Ft
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi δ))) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
          (r * p.2 + r) (r * p.2))
        ((volume.restrict (Set.Icc c₀ c₁)).prod
          (volume.restrict (Set.Ioi ((1 / hughesYoungDyadicRatio) / r))))
    have hraw :=
      integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint_arbitraryStrip
        hc₀ hc hc₀one z t H
          (by simpa [abs_of_nonneg (zero_le_one.trans hH)] using hH)
          a b qx qy R K hr (T := T) (h := h) (k := k)
    refine hraw.congr ?_
    filter_upwards [] with p
    rfl
  have hrEdge : Integrable Fr
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi δ))) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₁ : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
          (r * p.2 + r) (r * p.2))
        ((volume.restrict (Set.Icc (-H) H)).prod
          (volume.restrict (Set.Ioi ((1 / hughesYoungDyadicRatio) / r))))
    have hraw :=
      integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint_arbitraryStrip
        hc₀ hc₀one (show c₁ ∈ Set.Icc c₀ c₁ from ⟨hc, le_rfl⟩)
          z t H a b qx qy R K hr (T := T) (h := h) (k := k)
    refine hraw.congr ?_
    filter_upwards [] with p
    rfl
  have hlEdge : Integrable Fl
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi δ))) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₀ : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
          (r * p.2 + r) (r * p.2))
        ((volume.restrict (Set.Icc (-H) H)).prod
          (volume.restrict (Set.Ioi ((1 / hughesYoungDyadicRatio) / r))))
    have hraw :=
      integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint_arbitraryStrip
        hc₀ hc₀one (show c₀ ∈ Set.Icc c₀ c₁ from ⟨le_rfl, hc⟩)
          z t H a b qx qy R K hr (T := T) (h := h) (k := k)
    refine hraw.congr ?_
    filter_upwards [] with p
    rfl
  have hswapB :
      (∫ s : ℝ in Set.Icc c₀ c₁, ∫ x : ℝ in Set.Ioi δ, Fb (s, x)) =
        ∫ x : ℝ in Set.Ioi δ, ∫ s : ℝ in Set.Icc c₀ c₁, Fb (s, x) :=
    integral_integral_swap hb
  have hswapT :
      (∫ s : ℝ in Set.Icc c₀ c₁, ∫ x : ℝ in Set.Ioi δ, Ft (s, x)) =
        ∫ x : ℝ in Set.Ioi δ, ∫ s : ℝ in Set.Icc c₀ c₁, Ft (s, x) :=
    integral_integral_swap ht
  have hswapR :
      (∫ u : ℝ in Set.Icc (-H) H, ∫ x : ℝ in Set.Ioi δ, Fr (u, x)) =
        ∫ x : ℝ in Set.Ioi δ, ∫ u : ℝ in Set.Icc (-H) H, Fr (u, x) :=
    integral_integral_swap hrEdge
  have hswapL :
      (∫ u : ℝ in Set.Icc (-H) H, ∫ x : ℝ in Set.Ioi δ, Fl (u, x)) =
        ∫ x : ℝ in Set.Ioi δ, ∫ u : ℝ in Set.Icc (-H) H, Fl (u, x) :=
    integral_integral_swap hlEdge
  have hpoint (x : ℝ) :
      (∫ s : ℝ in Set.Icc c₀ c₁, Fb (s, x)) -
        (∫ s : ℝ in Set.Icc c₀ c₁, Ft (s, x)) +
        I • (∫ u : ℝ in Set.Icc (-H) H, Fr (u, x)) -
        I • (∫ u : ℝ in Set.Icc (-H) H, Fl (u, x)) = 0 := by
    have hz :=
      dfiEquation27C_scalar_mul_nonLowerActiveComplement_boundaryRect_zero
        T t z h k a b qx qy R K (r * x + r) (r * x) hc₀ hc (H := H)
    simpa only [Fb, Ft, Fr, Fl,
      intervalIntegral.integral_of_le hc,
      intervalIntegral.integral_of_le (by linarith : -H ≤ H),
      restrict_Ioc_eq_restrict_Icc] using hz
  have hBinterval :
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi δ, Fb (s, x)) =
        ∫ s : ℝ in Set.Icc c₀ c₁, ∫ x : ℝ in Set.Ioi δ, Fb (s, x) := by
    rw [intervalIntegral.integral_of_le hc, restrict_Ioc_eq_restrict_Icc]
  have hTinterval :
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi δ, Ft (s, x)) =
        ∫ s : ℝ in Set.Icc c₀ c₁, ∫ x : ℝ in Set.Ioi δ, Ft (s, x) := by
    rw [intervalIntegral.integral_of_le hc, restrict_Ioc_eq_restrict_Icc]
  have hRinterval :
      (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi δ, Fr (u, x)) =
        ∫ u : ℝ in Set.Icc (-H) H, ∫ x : ℝ in Set.Ioi δ, Fr (u, x) := by
    rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
      restrict_Ioc_eq_restrict_Icc]
  have hLinterval :
      (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi δ, Fl (u, x)) =
        ∫ u : ℝ in Set.Icc (-H) H, ∫ x : ℝ in Set.Ioi δ, Fl (u, x) := by
    rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
      restrict_Ioc_eq_restrict_Icc]
  rw [hBinterval, hTinterval, hRinterval, hLinterval]
  rw [hswapB, hswapT, hswapR, hswapL]
  simp only [smul_eq_mul]
  have hBT := hb.integral_prod_right.sub ht.integral_prod_right
  have hIR := hrEdge.integral_prod_right.const_mul I
  have hIL := hlEdge.integral_prod_right.const_mul I
  have hBTIR := hBT.add hIR
  have hzeroIntegral :
      (∫ x : ℝ in Set.Ioi δ,
        ((∫ s : ℝ in Set.Icc c₀ c₁, Fb (s, x)) -
          (∫ s : ℝ in Set.Icc c₀ c₁, Ft (s, x)) +
          I * (∫ u : ℝ in Set.Icc (-H) H, Fr (u, x)) -
          I * (∫ u : ℝ in Set.Icc (-H) H, Fl (u, x)))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    simpa only [smul_eq_mul] using hpoint x
  have hzeroAlgebraic :
      (∫ x : ℝ in Set.Ioi δ,
        ((((fun y : ℝ => ∫ s : ℝ in Set.Icc c₀ c₁, Fb (s, y)) -
              (fun y : ℝ => ∫ s : ℝ in Set.Icc c₀ c₁, Ft (s, y))) +
            (fun y : ℝ => I *
              (∫ u : ℝ in Set.Icc (-H) H, Fr (u, y)))) -
          (fun y : ℝ => I *
            (∫ u : ℝ in Set.Icc (-H) H, Fl (u, y)))) x) = 0 := by
    simpa only [Pi.sub_apply, Pi.add_apply] using hzeroIntegral
  have hSubBT := integral_sub hb.integral_prod_right ht.integral_prod_right
  have hAddR := integral_add hBT hIR
  have hSubL := integral_sub hBTIR hIL
  have hMulR := MeasureTheory.integral_const_mul
    (μ := volume.restrict (Set.Ioi δ)) I
    (fun x : ℝ => ∫ u : ℝ in Set.Icc (-H) H, Fr (u, x))
  have hMulL := MeasureTheory.integral_const_mul
    (μ := volume.restrict (Set.Ioi δ)) I
    (fun x : ℝ => ∫ u : ℝ in Set.Icc (-H) H, Fl (u, x))
  linear_combination hzeroAlgebraic - hSubL - hAddR - hSubBT - hMulR + hMulL


/-- Exact equation-(27) central-integral contour identity on an arbitrary
compact positive Mellin strip. -/
theorem dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_boundaryRect_zero_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t : ℝ) {H : ℝ} (hH : 1 ≤ H)
    (h k a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..c₁,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
              h k a b R K X Y) r) -
      (∫ s : ℝ in c₀..c₁,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + (H : ℂ) * I)
              h k a b R K X Y) r) +
      I • (∫ u : ℝ in -H..H,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₁ : ℂ) + (u : ℂ) * I)
              h k a b R K X Y) r) -
      I • (∫ u : ℝ in -H..H,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₀ : ℂ) + (u : ℂ) * I)
              h k a b R K X Y) r) = 0 := by
  have hrect :=
    integral_dfiEquation27C_scalar_mul_nonLowerActiveComplement_dilated_boundaryRect_zero_arbitraryStrip
      hc₀ hc hc₀one z t hH h k a b qx qy R K hr (T := T)
  have hcentral (w : ℂ) :=
    dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
      T t w z h k a b qx qy R K hr
  simp only [smul_eq_mul]
  simp_rw [hcentral, intervalIntegral.integral_const_mul]
  linear_combination (r : ℂ) * hrect


/-- Every scalar positive-shift equation-(27) modulus summand has zero
integral around an arbitrary compact positive Mellin rectangle. -/
theorem hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_boundaryRect_zero_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t : ℝ) {H : ℝ} (hH : 1 ≤ H)
    (h k a b R K : ℕ) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    (∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r q) -
      (∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r q) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((c₁ : ℂ) + (u : ℂ) * I)
          h k a b R K r q) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r q) = 0 := by
  have hcentral :=
    dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_boundaryRect_zero_arbitraryStrip
      hc₀ hc hc₀one z t hH h k a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        R K (show (0 : ℝ) < r by exact_mod_cast hr) (T := T)
  let z : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  simp only [smul_eq_mul]
  simp_rw [intervalIntegral.integral_const_mul]
  change z * _ - z * _ + I * (z * _) - I * (z * _) = 0
  linear_combination z * hcentral


/-- Horizontal interval integrability of one scalar modulus summand on an
arbitrary positive Mellin strip in the contour-exhaustion range. -/
theorem intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t H : ℝ) (hH : 1 ≤ |H|)
    (h k a b R K : ℕ)
    {r : ℕ} (hr : 0 < r) (q : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q)
      volume c₀ c₁ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hjoint :=
    integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint_arbitraryStrip
      hc₀ hc hc₀one z t H hH a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR
      (T := T) (h := h) (k := k)
  let coeff : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have hinner := hjoint.integral_prod_left
  have hscaled := (hinner.const_mul (r : ℂ)).const_mul coeff
  have hinterval : IntervalIntegrable
      (fun s : ℝ => coeff * ((r : ℂ) *
        ∫ x : ℝ in Set.Ioi ((1 / hughesYoungDyadicRatio) / (r : ℝ)),
          dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (fun X Y => z *
              hughesYoungNonLowerActiveComplementMellinWeightComplex T t
                ((s : ℂ) + (H : ℂ) * I) h k a b R K X Y)
            ((r : ℝ) * x + r) ((r : ℝ) * x))) volume c₀ c₁ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    exact hscaled
  convert hinterval using 1
  funext s
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
    T t ((s : ℂ) + (H : ℂ) * I) z h k a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR]
  dsimp only [coeff]
  push_cast
  ring


/-- Vertical interval integrability of one scalar modulus summand on any
edge of an arbitrary compact positive Mellin strip. -/
theorem intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_arbitraryStrip
    {T c₀ c₁ c : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    (hc : c ∈ Set.Icc c₀ c₁) (z : ℂ) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k a b R K : ℕ)
    {r : ℕ} (hr : 0 < r) (q : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q)
      volume (-H) H := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hjoint :=
    integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint_arbitraryStrip
      hc₀ hc₀one hc z t H a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR
      (T := T) (h := h) (k := k)
  let coeff : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have hinner := hjoint.integral_prod_left
  have hscaled := (hinner.const_mul (r : ℂ)).const_mul coeff
  have hinterval : IntervalIntegrable
      (fun u : ℝ => coeff * ((r : ℂ) *
        ∫ x : ℝ in Set.Ioi ((1 / hughesYoungDyadicRatio) / (r : ℝ)),
          dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (fun X Y => z *
              hughesYoungNonLowerActiveComplementMellinWeightComplex T t
                ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
            ((r : ℝ) * x + r) ((r : ℝ) * x))) volume (-H) H := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -H ≤ H)]
    exact hscaled
  convert hinterval using 1
  funext u
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
    T t ((c : ℂ) + (u : ℂ) * I) z h k a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR]
  dsimp only [coeff]
  push_cast
  ring


/-- Fixed-height, modulus-uniform horizontal majorant on an arbitrary
positive Mellin strip. -/
theorem exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t H : ℝ) (hH : 1 ≤ |H|)
    (h k : ℕ) {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (R K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) (c : ℝ), c ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r q‖ ≤
      B * (((q : ℝ) ^ 2)⁻¹ *
        (hughesYoungEquation84LogBudget a b r +
          4 * Real.log (q : ℝ)) ^ 2) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le_arbitraryStripGaussian
      hc₀ hc hc₀one z t h k ha hb hr R K (T := T)
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  refine ⟨D * E, mul_nonneg hD.le (by dsimp only [E]; positivity), ?_⟩
  intro q c hcMem
  simpa only [E, mul_assoc] using hbound H hH q c hcMem

set_option maxHeartbeats 1200000 in
theorem summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t H : ℝ) (hH : 1 ≤ |H|) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (R K : ℕ) :
    Summable (fun q : ℕ =>
      ∫ s : ℝ in Set.Icc c₀ c₁,
        ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q‖) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le_arbitraryStrip
      hc₀ hc hc₀one z t H hH h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hmajor : Summable (fun q : ℕ => (c₁ - c₀) * M q) := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left
        ((c₁ - c₀) * B)
    simpa only [M, mul_assoc] using hbase
  apply hmajor.of_nonneg_of_le
  · intro q
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun s => norm_nonneg _)
  · intro q
    let f : ℝ → ℂ := fun s =>
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
    have hfInterval :=
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
        hc₀ hc hc₀one z t H hH h k a b R K hr q (T := T)
    have hf : Integrable f (volume.restrict (Set.Icc c₀ c₁)) := by
      change IntegrableOn f (Set.Icc c₀ c₁)
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hc]
      exact hfInterval
    have hM0 : 0 ≤ M q := by
      dsimp only [M]
      positivity
    have hconst : Integrable (fun _s : ℝ => M q)
        (volume.restrict (Set.Icc c₀ c₁)) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    calc
      (∫ s : ℝ in Set.Icc c₀ c₁, ‖f s‖) ≤
          ∫ _s : ℝ in Set.Icc c₀ c₁, M q := by
        apply MeasureTheory.integral_mono_ae hf.norm hconst
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        simpa only [f, M, A] using hbound q s hs
      _ = (c₁ - c₀) * M q := by
        simp [MeasureTheory.integral_const, hc]


/-- Pointwise opening-line conductor saving for the exact DFI-dilated
non-lower complement.  This is the quantitative form of the support
vanishing used in the contour move. -/
theorem nonLowerActiveComplementMultiplier_mul_norm_dilatedBeta_le
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u c : ℝ) {η r x : ℝ} (hη : 0 ≤ η) (hr : 0 < r) (hx : 0 < x)
    (CX COne : ℂ) :
    hughesYoungNonLowerActiveComplementMultiplier a b R K
          (r * x + r) (r * x) *
        ‖(r : ℂ) ^ (-(afeCriticalPoint t +
              ((c : ℂ) + (u : ℂ) * I))) *
            (r : ℂ) ^ (-(afeCriticalPoint (-t) +
              ((c : ℂ) + (u : ℂ) * I))) *
            hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
      (((a * b * R : ℕ) : ℝ) ^ (-η)) *
        ‖(r : ℂ) ^ (-(afeCriticalPoint t +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            (r : ℂ) ^ (-(afeCriticalPoint (-t) +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            hughesYoungCriticalAffineBetaIntegrand
              t u (c - η) x CX COne‖ := by
  let A : ℝ := ((a * b * R : ℕ) : ℝ)
  let X : ℝ := (r * x + r) * (r * x)
  let F : ℝ → ℝ := fun d =>
    ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((d : ℂ) + (u : ℂ) * I))) *
      (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((d : ℂ) + (u : ℂ) * I))) *
      hughesYoungCriticalAffineBetaIntegrand t u d x CX COne‖
  have hA : 0 < A := by dsimp only [A]; positivity
  have hleft : 0 ≤ r * x + r := (add_pos (mul_pos hr hx) hr).le
  have hright : 0 ≤ r * x := (mul_pos hr hx).le
  have hX : 0 < X := by
    dsimp only [X]
    exact mul_pos (add_pos (mul_pos hr hx) hr) (mul_pos hr hx)
  have hm :=
    hughesYoungNonLowerActiveComplementMultiplier_le_productRatio_rpow
      ha hb hR hleft hright hη hstrong
  have hshift : X ^ η * F c = F (c - η) := by
    dsimp only [X, F]
    exact rpow_mul_norm_hughesYoungDilatedCriticalAffineBeta_eq_shift
      t u c η hr hx CX COne
  change hughesYoungNonLowerActiveComplementMultiplier a b R K
      (r * x + r) (r * x) * F c ≤ A ^ (-η) * F (c - η)
  calc
    hughesYoungNonLowerActiveComplementMultiplier a b R K
          (r * x + r) (r * x) * F c ≤
        (X / A) ^ η * F c :=
      mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ = A ^ (-η) * (X ^ η * F c) := by
      rw [Real.div_rpow hX.le hA.le, Real.rpow_neg hA.le]
      field_simp
    _ = A ^ (-η) * F (c - η) := by rw [hshift]

/-- DFI equation-(27) integrand on the opening line, with its full
logarithmic factors, inherits the conductor saving from the exact active
complement support. -/
theorem norm_dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_le
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u c : ℝ) {η r x : ℝ} (hη : 0 ≤ η) (hr : 0 < r) (hx : 0 < x)
    (qx qy : ℕ) :
    ‖dfiEquation27C a b qx qy
        (hughesYoungNonLowerActiveComplementMellinShapeComplex
          t ((c : ℂ) + (u : ℂ) * I) a b R K)
        (r * x + r) (r * x)‖ ≤
      (((a * b * R : ℕ) : ℝ) ^ (-η)) *
        ‖(r : ℂ) ^ (-(afeCriticalPoint t +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            (r : ℂ) ^ (-(afeCriticalPoint (-t) +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            hughesYoungCriticalAffineBetaIntegrand t u (c - η) x
              ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
              ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖ := by
  have hleft : 0 ≤ r * x + r := (add_pos (mul_pos hr hx) hr).le
  have hright : 0 ≤ r * x := (mul_pos hr hx).le
  have hm0 := hughesYoungNonLowerActiveComplementMultiplier_nonneg
    a b R K hleft hright
  rw [dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
    t c u a b qx qy R K hr hx]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  simpa only [norm_mul, mul_assoc] using
    nonLowerActiveComplementMultiplier_mul_norm_dilatedBeta_le
      ha hb hR hstrong t u c hη hr hx
        ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
        ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)

/-- The source-facing version of the preceding inequality, including the
literal height cutoff and reduced Hughes--Young Mellin scalar. -/
theorem norm_dfiEquation27C_heightWeight_mul_nonLowerActiveComplement_dilate_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u c : ℝ) (h k : ℕ) {η r x : ℝ}
    (hη : 0 ≤ η) (hr : 0 < r) (hx : 0 < x) (qx qy : ℕ) :
    ‖dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)‖ ≤
      ‖hughesYoungHeightWeight T t‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        (((a * b * R : ℕ) : ℝ) ^ (-η)) *
        ‖(r : ℂ) ^ (-(afeCriticalPoint t +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            (r : ℂ) ^ (-(afeCriticalPoint (-t) +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            hughesYoungCriticalAffineBetaIntegrand t u (c - η) x
              ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
              ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖ := by
  have heq :
      dfiEquation27C a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
          (r * x + r) (r * x) =
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungReducedMellinScaleConstantComplex T t
            ((c : ℂ) + (u : ℂ) * I) h k *
          dfiEquation27C a b qx qy
            (hughesYoungNonLowerActiveComplementMellinShapeComplex
              t ((c : ℂ) + (u : ℂ) * I) a b R K)
            (r * x + r) (r * x) := by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring
  rw [heq]
  have hshape :=
    norm_dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_le
      ha hb hR hstrong t u c hη hr hx qx qy
  calc
    ‖(hughesYoungHeightWeight T t : ℂ) *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (u : ℂ) * I) a b R K)
          (r * x + r) (r * x)‖ =
      ‖hughesYoungHeightWeight T t‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        ‖dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (u : ℂ) * I) a b R K)
          (r * x + r) (r * x)‖ := by
        simp only [norm_mul, Complex.norm_real]
    _ ≤ ‖hughesYoungHeightWeight T t‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        ((((a * b * R : ℕ) : ℝ) ^ (-η)) *
          ‖(r : ℂ) ^ (-(afeCriticalPoint t +
                (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
              (r : ℂ) ^ (-(afeCriticalPoint (-t) +
                (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
              hughesYoungCriticalAffineBetaIntegrand t u (c - η) x
                ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
                ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖) :=
      mul_le_mul_of_nonneg_left hshape
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- Scalar-parametric form of the opening-line conductor saving.  This is
needed for the negative DFI shift, where the physical height cutoff remains
at `t` while the two critical-line parameters are interchanged and hence the
Mellin kernel is evaluated at `-t`. -/
theorem norm_dfiEquation27C_scalar_mul_nonLowerActiveComplement_dilate_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) (t u c : ℝ) (h k : ℕ) {η r x : ℝ}
    (hη : 0 ≤ η) (hr : 0 < r) (hx : 0 < x) (qx qy : ℕ) :
    ‖dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)‖ ≤
      ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        (((a * b * R : ℕ) : ℝ) ^ (-η)) *
        ‖(r : ℂ) ^ (-(afeCriticalPoint t +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            (r : ℂ) ^ (-(afeCriticalPoint (-t) +
              (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
            hughesYoungCriticalAffineBetaIntegrand t u (c - η) x
              ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
              ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖ := by
  have heq :
      dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
          (r * x + r) (r * x) =
        z *
          hughesYoungReducedMellinScaleConstantComplex T t
            ((c : ℂ) + (u : ℂ) * I) h k *
          dfiEquation27C a b qx qy
            (hughesYoungNonLowerActiveComplementMellinShapeComplex
              t ((c : ℂ) + (u : ℂ) * I) a b R K)
            (r * x + r) (r * x) := by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring
  rw [heq]
  have hshape :=
    norm_dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_le
      ha hb hR hstrong t u c hη hr hx qx qy
  calc
    ‖z *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (u : ℂ) * I) a b R K)
          (r * x + r) (r * x)‖ =
      ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        ‖dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (u : ℂ) * I) a b R K)
          (r * x + r) (r * x)‖ := by simp only [norm_mul]
    _ ≤ ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        ((((a * b * R : ℕ) : ℝ) ^ (-η)) *
          ‖(r : ℂ) ^ (-(afeCriticalPoint t +
                (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
              (r : ℂ) ^ (-(afeCriticalPoint (-t) +
                (((c - η : ℝ) : ℂ) + (u : ℂ) * I))) *
              hughesYoungCriticalAffineBetaIntegrand t u (c - η) x
                ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
                ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖) :=
      mul_le_mul_of_nonneg_left hshape
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- On an arbitrary even Hughes--Young opening line, every positive-shift
equation-(27) modulus summand gains the full conductor power
`(abR)^(-(2Q-1/2))`.  The affine-beta kernel is moved back to the fixed
integrable line `Re w = 1/2`; all remaining dependence is displayed
literally. -/
theorem norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_even_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ)
    {r q : ℕ} (hr : 0 < r) :
    ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r q‖ ≤
      ‖((a : ℂ) * b)⁻¹‖ *
        (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
        ((r : ℝ) *
          (‖z‖ *
            ‖hughesYoungReducedMellinScaleConstantComplex T t
              (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖ *
            (((a * b * R : ℕ) : ℝ) ^
              (-(2 * (Q : ℝ) - 1 / 2))) *
            ((r : ℝ) ^ (-2 : ℝ)) *
            ((2312 * max 1
                ((((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                  (-(3 / 4 : ℝ)))) + 72) *
              (hughesYoungEquation84LogBudget a b r +
                4 * Real.log (q : ℝ)) ^ 2))) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let delta : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
    let eta : ℝ := 2 * (Q : ℝ) - 1 / 2
    let qx : ℕ := dfiReducedDenominator a q
    let qy : ℕ := dfiReducedDenominator b q
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
    let F : ℝ → ℂ := fun x =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k a b R K X Y)
        ((r : ℝ) * x + r) ((r : ℝ) * x)
    let J : ℝ → ℂ := fun x => (Set.Ioi delta).indicator F x
    let D : ℝ :=
      ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖ *
        (((a * b * R : ℕ) : ℝ) ^ (-eta)) *
        ((r : ℝ) ^ (-2 : ℝ))
    have hdelta : 0 < delta := div_pos
      (one_div_pos.mpr hughesYoungDyadicRatio_pos) hrR
    have heta : 0 ≤ eta := by
      dsimp only [eta]
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have hline : (((2 * Q : ℕ) : ℝ)) - eta = 1 / 2 := by
      dsimp only [eta]
      push_cast
      ring
    have hGint : Integrable
        (hughesYoungCriticalAffineBetaFullStripMajorant
          (1 / 2) delta S) :=
      integrable_hughesYoungCriticalAffineBetaFullStripMajorant (by norm_num)
    have hD0 : 0 ≤ D := by dsimp only [D]; positivity
    have hDGint : Integrable (fun x : ℝ =>
        D * hughesYoungCriticalAffineBetaFullStripMajorant
          (1 / 2) delta S x) := hGint.const_mul D
    have hJbound (x : ℝ) :
        ‖J x‖ ≤ D *
          hughesYoungCriticalAffineBetaFullStripMajorant
            (1 / 2) delta S x := by
      by_cases hxmem : x ∈ Set.Ioi delta
      · have hx : 0 < x := hdelta.trans hxmem
        have hsource :=
          norm_dfiEquation27C_scalar_mul_nonLowerActiveComplement_dilate_le
            (T := T) ha hb hR hstrong z t u (((2 * Q : ℕ) : ℝ)) h k
              heta hrR hx qx qy
        have hrpow :=
          norm_hughesYoungDilationPowerPair_horizontal
            t (1 / 2) u hrR
        have hbeta :=
          norm_hughesYoungCriticalAffineBetaIntegrand_le_fullStripMajorant
            (t := t) (u := u) (c₀ := (1 / 2 : ℝ)) (c := (1 / 2 : ℝ))
            (δ := delta) (x := x)
            (CX := (Real.log r : ℂ) + dfiEquation27LogConstant b qy)
            (COne := (Real.log r : ℂ) + dfiEquation27LogConstant a qx)
            (by norm_num) le_rfl (by norm_num) hdelta hxmem
        have hkernel :
            ‖((r : ℝ) : ℂ) ^ (-(afeCriticalPoint t +
                  (((((2 * Q : ℕ) : ℝ) - eta : ℝ) : ℂ) + (u : ℂ) * I))) *
                ((r : ℝ) : ℂ) ^ (-(afeCriticalPoint (-t) +
                  (((((2 * Q : ℕ) : ℝ) - eta : ℝ) : ℂ) + (u : ℂ) * I))) *
                hughesYoungCriticalAffineBetaIntegrand
                  t u (((2 * Q : ℕ) : ℝ) - eta) x
                    ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
                    ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖ ≤
              (r : ℝ) ^ (-2 : ℝ) *
                hughesYoungCriticalAffineBetaFullStripMajorant
                  (1 / 2) delta S x := by
          rw [hline]
          rw [norm_mul]
          calc
            ‖((r : ℝ) : ℂ) ^ (-(afeCriticalPoint t +
                    (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))) *
                  ((r : ℝ) : ℂ) ^ (-(afeCriticalPoint (-t) +
                    (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)))‖ *
                ‖hughesYoungCriticalAffineBetaIntegrand t u (1 / 2) x
                    ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
                    ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖ ≤
              (r : ℝ) ^ (-2 : ℝ) *
                hughesYoungCriticalAffineBetaFullStripMajorant
                  (1 / 2) delta S x := by
                rw [hrpow]
                rw [show -(1 + 2 * (1 / 2 : ℝ)) = (-2 : ℝ) by norm_num]
                gcongr
            _ = _ := rfl
        rw [hline] at hkernel
        have hJ : J x = F x := by simp [J, hxmem]
        rw [hJ]
        rw [hline] at hsource
        refine hsource.trans ?_
        dsimp only [D, eta]
        have hpre : 0 ≤
            ‖z‖ *
              ‖hughesYoungReducedMellinScaleConstantComplex T t
                (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖ *
              (((a * b * R : ℕ) : ℝ) ^
                (-(2 * (Q : ℝ) - 1 / 2))) :=
          mul_nonneg
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        have hmul := mul_le_mul_of_nonneg_left hkernel hpre
        convert hmul using 1
        all_goals ring
      · have hJ : J x = 0 := by simp [J, hxmem]
        rw [hJ, norm_zero]
        exact mul_nonneg hD0
          hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    have hIntRaw := MeasureTheory.norm_integral_le_of_norm_le hDGint
      (Filter.Eventually.of_forall hJbound)
    have hInt :
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ ≤
          D * (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) * S ^ 2 +
            72 * S ^ 2) := by
      calc
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ = ‖∫ x : ℝ, J x‖ := by
          simp only [J, MeasureTheory.integral_indicator measurableSet_Ioi]
        _ ≤ ∫ x : ℝ,
            D * hughesYoungCriticalAffineBetaFullStripMajorant
              (1 / 2) delta S x := hIntRaw
        _ = D * ∫ x : ℝ,
            hughesYoungCriticalAffineBetaFullStripMajorant
              (1 / 2) delta S x := by
          rw [MeasureTheory.integral_const_mul]
        _ = D * (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) * S ^ 2 +
            72 * S ^ 2) := by
          rw [integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq
            (by norm_num : (0 : ℝ) < 1 / 2)]
          ring_nf
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    let A : ℝ := hughesYoungEquation84LogBudget a b r
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A, qx, qy]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCentral :=
      dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
        T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) z
          h k a b qx qy R K hrR
    unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      dfiEquation27CentralSummand
    rw [hCentral]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrR]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((r : ℝ) * ‖∫ x : ℝ in Set.Ioi delta, F x‖) ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) * S ^ 2 +
              72 * S ^ 2))) := by gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * ((2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) + 72) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) * S ^ 2 + 72 * S ^ 2 =
              (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) + 72) * S ^ 2 := by ring
          _ ≤ (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) + 72) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = _ := by
        dsimp only [D, eta, delta, A]

/-- Physical-height specialization of the scalar opening-line summand
estimate. -/
theorem norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_even_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ)
    {r q : ℕ} (hr : 0 < r) :
    ‖hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
        T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r q‖ ≤
      ‖((a : ℂ) * b)⁻¹‖ *
        (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
        ((r : ℝ) *
          (‖hughesYoungHeightWeight T t‖ *
            ‖hughesYoungReducedMellinScaleConstantComplex T t
              (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖ *
            (((a * b * R : ℕ) : ℝ) ^
              (-(2 * (Q : ℝ) - 1 / 2))) *
            ((r : ℝ) ^ (-2 : ℝ)) *
            ((2312 * max 1
                ((((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                  (-(3 / 4 : ℝ)))) + 72) *
              (hughesYoungEquation84LogBudget a b r +
                4 * Real.log (q : ℝ)) ^ 2))) := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)] using
    norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_even_le
      (T := T) (q := q) ha hb hR hstrong
        (hughesYoungHeightWeight T t : ℂ) hQ t u h k hr

/-- The `q`-independent factor in the scalar-parametric opening-line
estimate. -/
noncomputable def hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
    (z : ℂ) (T t u : ℝ) (Q h k a b R r : ℕ) : ℝ :=
  ‖((a : ℂ) * b)⁻¹‖ * (((a * b * r ^ 2 : ℕ) : ℝ)) * (r : ℝ) *
    (‖z‖ *
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖ *
      (((a * b * R : ℕ) : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2))) *
      ((r : ℝ) ^ (-2 : ℝ)) *
      (2312 * max 1
          (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
            (-(3 / 4 : ℝ))) + 72))

theorem hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_nonneg
    (z : ℂ) (T t u : ℝ) (Q h k a b R r : ℕ) :
    0 ≤ hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
      z T t u Q h k a b R r := by
  unfold hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
  positivity

/-- Modulus-separated scalar-parametric opening-line estimate. -/
theorem norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_even_le_prefactor
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ)
    {r : ℕ} (hr : 0 < r) (q : ℕ) :
    ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r q‖ ≤
      hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
          z T t u Q h k a b R r *
        (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  refine
    (norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_even_le
      ha hb hR hstrong z hQ t u h k hr).trans_eq ?_
  unfold hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
  ring

/-- On the even opening line, the reduced Mellin scale is uniformly bounded
on a compact vertical edge; consequently the complete modulus profile has a
single constant independent of the modulus and ordinate. -/
theorem exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_even_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t : ℝ) (H : ℝ)
    (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) (u : ℝ), u ∈ Set.Icc (-H) H →
      ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r q‖ ≤
      B * (((q : ℝ) ^ 2)⁻¹ *
        (hughesYoungEquation84LogBudget a b r +
          4 * Real.log (q : ℝ)) ^ 2) := by
  have hc : 0 < (((2 * Q : ℕ) : ℝ)) := by positivity
  obtain ⟨Cs, hCs, hscale⟩ :=
    exists_uniform_norm_hughesYoungReducedMellinScaleConstantComplex_vertical
      T t (((2 * Q : ℕ) : ℝ)) H h k hc
  let B : ℝ := ‖((a : ℂ) * b)⁻¹‖ * (((a * b * r ^ 2 : ℕ) : ℝ)) *
    (r : ℝ) *
    (‖z‖ * Cs *
      (((a * b * R : ℕ) : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2))) *
      ((r : ℝ) ^ (-2 : ℝ)) *
      (2312 * max 1
          (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
            (-(3 / 4 : ℝ))) + 72))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro q u hu
  have hraw :=
    norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_even_le_prefactor
      (T := T) ha hb hR hstrong z hQ t u h k hr q
  refine hraw.trans ?_
  unfold hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
  have hprofile : 0 ≤ ((q : ℝ) ^ 2)⁻¹ *
      (hughesYoungEquation84LogBudget a b r +
        4 * Real.log (q : ℝ)) ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_right _ hprofile
  dsimp only [B]
  gcongr
  exact hscale u hu


set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1200000 in
theorem summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    Summable (fun q : ℕ =>
      ∫ u : ℝ in Set.Icc (-H) H,
        ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r q‖) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_even_le
      ha hb hR hstrong z hQ t H h k hr (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hmajor : Summable (fun q : ℕ => (H - (-H)) * M q) := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left
        ((H - (-H)) * B)
    simpa only [M, mul_assoc] using hbase
  apply hmajor.of_nonneg_of_le
  · intro q
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun u => norm_nonneg _)
  · intro q
    let f : ℝ → ℂ := fun u =>
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r q
    have horder : -H ≤ H := by linarith
    have hline : (1 / 2 : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := by
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      push_cast
      linarith
    have hfInterval :=
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_arbitraryStrip
        (T := T) (c₀ := (1 / 2 : ℝ)) (c₁ := ((2 * Q : ℕ) : ℝ))
        (c := ((2 * Q : ℕ) : ℝ)) (by norm_num) (by norm_num)
        ⟨hline, le_rfl⟩ z t hH h k a b R K hr q
    have hf : Integrable f (volume.restrict (Set.Icc (-H) H)) := by
      change IntegrableOn f (Set.Icc (-H) H)
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le horder]
      exact hfInterval
    have hM0 : 0 ≤ M q := by dsimp only [M]; positivity
    have hconst : Integrable (fun _u : ℝ => M q)
        (volume.restrict (Set.Icc (-H) H)) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    calc
      (∫ u : ℝ in Set.Icc (-H) H, ‖f u‖) ≤
          ∫ _u : ℝ in Set.Icc (-H) H, M q := by
        apply MeasureTheory.integral_mono_ae hf.norm hconst
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        simpa only [f, M, A] using hbound q u hu
      _ = (H - (-H)) * M q := by
        simp [MeasureTheory.integral_const, hH]


theorem summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t H : ℝ) (hH : 1 ≤ |H|) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ => ∫ s : ℝ in c₀..c₁,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q) := by
  have hNorm :=
    summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
      hc₀ hc hc₀one z t H hH h k ha hb hr R K (T := T)
  apply Summable.of_norm_bounded hNorm
  intro q
  rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.norm_integral_le_integral_norm _


theorem summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    Summable (fun q : ℕ => ∫ u : ℝ in -H..H,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r q) := by
  have hNorm :=
    summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_even
      ha hb hR hstrong z hQ t hH h k hr (T := T)
  have horder : -H ≤ H := by linarith
  apply Summable.of_norm_bounded hNorm
  intro q
  rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.norm_integral_le_integral_norm _


theorem integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t H : ℝ) (hH : 1 ≤ |H|) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    (∫ s : ℝ in c₀..c₁,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) =
      ∑' q : ℕ, ∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q := by
  let F : ℕ → ℝ → ℂ := fun q s =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
  have hInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc c₀ c₁)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc c₀ c₁)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    simpa only [F] using
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
        hc₀ hc hc₀one z t H hH h k a b R K hr q (T := T)
  have hNorm : Summable (fun q : ℕ =>
      ∫ s : ℝ in Set.Icc c₀ c₁, ‖F q s‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
        hc₀ hc hc₀one z t H hH h k ha hb hr R K (T := T)
  have hswap : (∑' q : ℕ, ∫ s : ℝ in Set.Icc c₀ c₁, F q s) =
      ∫ s : ℝ in Set.Icc c₀ c₁, ∑' q : ℕ, F q s :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hInt hNorm
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
  rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ s : ℝ in Set.Icc c₀ c₁, ∑' q : ℕ, F q s) =
        ∑' q : ℕ, ∫ s : ℝ in Set.Icc c₀ c₁, F q s := hswap.symm
    _ = ∑' q : ℕ, ∫ s : ℝ in c₀..c₁, F q s := by
      apply tsum_congr
      intro q
      rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]


set_option maxHeartbeats 1200000 in
theorem integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    (∫ u : ℝ in -H..H,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r) =
      ∑' q : ℕ, ∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r q := by
  have horder : -H ≤ H := by linarith
  let F : ℕ → ℝ → ℂ := fun q u =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
        h k a b R K r q
  have hInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc (-H) H)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc (-H) H)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le horder]
    simpa only [F] using
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_arbitraryStrip
        (T := T) (c₀ := (1 / 2 : ℝ)) (c₁ := ((2 * Q : ℕ) : ℝ))
        (c := ((2 * Q : ℕ) : ℝ)) (by norm_num) (by norm_num)
        ⟨(by have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
             push_cast
             linarith), le_rfl⟩
        z t hH h k a b R K hr q
  have hNorm : Summable (fun q : ℕ =>
      ∫ u : ℝ in Set.Icc (-H) H, ‖F q u‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_even
        ha hb hR hstrong z hQ t hH h k hr (T := T)
  have hswap : (∑' q : ℕ, ∫ u : ℝ in Set.Icc (-H) H, F q u) =
      ∫ u : ℝ in Set.Icc (-H) H, ∑' q : ℕ, F q u :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hInt hNorm
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
  rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ u : ℝ in Set.Icc (-H) H, ∑' q : ℕ, F q u) =
        ∑' q : ℕ, ∫ u : ℝ in Set.Icc (-H) H, F q u := hswap.symm
    _ = ∑' q : ℕ, ∫ u : ℝ in -H..H, F q u := by
      apply tsum_congr
      intro q
      rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]


set_option maxHeartbeats 2400000 in
/-- The complete scalar positive Ramanujan series has zero contour integral
between a low source line and the arbitrary even opening line. -/
theorem hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero_even
    {T c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t : ℝ)
    {H : ℝ} (hH : 1 ≤ H) (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r) -
      (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r) = 0 := by
  have hc : c₀ ≤ ((2 * Q : ℕ) : ℝ) := by
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    push_cast
    linarith
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hHabs : 1 ≤ |H| := by
    simpa [abs_of_nonneg hH₀] using hH
  let Bottom : ℕ → ℂ := fun q => ∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r q
  let Top : ℕ → ℂ := fun q => ∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
  let Right : ℕ → ℂ := fun q => ∫ u : ℝ in -H..H,
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k a b R K r q
  let Left : ℕ → ℂ := fun q => ∫ u : ℝ in -H..H,
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K r q
  have hBottom :=
    integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum_arbitraryStrip
      hc₀ hc hc₀one z t (-H) (by simpa using hHabs) h k ha hb hr R K (T := T)
  have hTop :=
    integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum_arbitraryStrip
      hc₀ hc hc₀one z t H hHabs h k ha hb hr R K (T := T)
  have hRight :=
    integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum_even
      ha hb hR hstrong z hQ t hH₀ h k hr (T := T)
  have hLeft :=
    integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum
      hc₀ hc₀one z t hH₀ h k ha hb hr R K (T := T)
  have hsBottom : Summable Bottom := by
    simpa only [Bottom] using
      summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
        hc₀ hc hc₀one z t (-H) (by simpa using hHabs) h k ha hb hr R K (T := T)
  have hsTop : Summable Top := by
    simpa only [Top] using
      summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
        hc₀ hc hc₀one z t H hHabs h k ha hb hr R K (T := T)
  have hsRight : Summable Right := by
    simpa only [Right] using
      summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_even
        ha hb hR hstrong z hQ t hH₀ h k hr (T := T)
  have hsLeft : Summable Left := by
    simpa only [Left] using
      summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc₀ hc₀one z t hH₀ h k ha hb hr R K (T := T)
  rw [hBottom, hTop, hRight, hLeft]
  simp only [smul_eq_mul]
  change (∑' q : ℕ, Bottom q) - (∑' q : ℕ, Top q) +
      I * (∑' q : ℕ, Right q) - I * (∑' q : ℕ, Left q) = 0
  calc
    _ = (∑' q : ℕ, (Bottom q - Top q)) +
        (∑' q : ℕ, (I * Right q - I * Left q)) := by
      rw [hsBottom.tsum_sub hsTop,
        (hsRight.mul_left I).tsum_sub (hsLeft.mul_left I),
        tsum_mul_left, tsum_mul_left]
      ring
    _ = ∑' q : ℕ,
        ((Bottom q - Top q) + (I * Right q - I * Left q)) := by
      rw [← (hsBottom.sub hsTop).tsum_add
        ((hsRight.mul_left I).sub (hsLeft.mul_left I))]
    _ = ∑' _q : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro q
      have hq :=
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_boundaryRect_zero_arbitraryStrip
          hc₀ hc hc₀one z t hH h k a b R K hr q (T := T)
      dsimp only [Bottom, Top, Right, Left]
      linear_combination hq
    _ = 0 := tsum_zero

/-- The physical positive Ramanujan series satisfies the arbitrary-even-line
contour identity. -/
theorem hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero_even
    {T c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) {H : ℝ} (hH : 1 ≤ H)
    (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) -
      (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K r) = 0 := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero_even
      hc₀ hc₀one ha hb hR hstrong (hughesYoungHeightWeight T t : ℂ)
        hQ t hH h k hr

/-- The coordinate-swapped negative Ramanujan series satisfies the same
arbitrary-even-line contour identity while retaining the original physical
height cutoff. -/
theorem hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_boundaryRect_zero_even
    {T c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) {H : ℝ} (hH : 1 ≤ H)
    (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r) -
      (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r) = 0 := by
  have hstrongSwap :
      hughesYoungDyadicRatio * ((b * a * R : ℕ) : ℝ) ≤
        hughesYoungDyadicRatio ^ (K + 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hstrong
  simp_rw [hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive]
  exact
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero_even
      hc₀ hc₀one hb ha hR hstrongSwap
        (hughesYoungHeightWeight T t : ℂ) hQ (-t) hH k h hr

set_option maxHeartbeats 1200000 in
/-- The complete scalar-parametric Ramanujan series is integrable on every
horizontal edge of a small Mellin rectangle.  The proof uses the same
inverse-square/log-square Weierstrass majorant as the exact contour swap. -/
theorem intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (z : ℂ) (t H : ℝ) (hH : 1 ≤ |H|) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r)
      volume c₀ c₁ := by
  let F : ℕ → ℝ → ℂ := fun q s =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
  obtain ⟨B, _hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le_arbitraryStrip
      hc₀ hc hc₀one z t H hH h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hM : Summable M := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left B
    simpa only [M, mul_assoc] using hbase
  have hFInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc c₀ c₁)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc c₀ c₁)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    simpa only [F] using
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_arbitraryStrip
        hc₀ hc hc₀one z t H hH h k a b R K hr q (T := T)
  have hmeas : AEStronglyMeasurable (fun s : ℝ => ∑' q : ℕ, F q s)
      (volume.restrict (Set.Icc c₀ c₁)) :=
    AEStronglyMeasurable.tsum (fun q => (hFInt q).aestronglyMeasurable)
  have hconst : Integrable (fun _s : ℝ => ∑' q : ℕ, M q)
      (volume.restrict (Set.Icc c₀ c₁)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc]
  change Integrable (fun s : ℝ => ∑' q : ℕ, F q s)
    (volume.restrict (Set.Icc c₀ c₁))
  apply hconst.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hnorm : Summable (fun q : ℕ => ‖F q s‖) :=
    hM.of_nonneg_of_le (fun q => norm_nonneg (F q s)) (fun q => by
      simpa only [F, M, A] using hbound q s hs)
  calc
    ‖∑' q : ℕ, F q s‖ ≤ ∑' q : ℕ, ‖F q s‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ℕ, M q :=
      hnorm.tsum_le_tsum (fun q => by
        simpa only [F, M, A] using hbound q s hs) hM


set_option maxHeartbeats 1200000 in
/-- Vertical-edge interval integrability of the complete scalar-parametric
Ramanujan series. -/
theorem intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r)
      volume (-H) H := by
  have horder : -H ≤ H := by linarith
  let F : ℕ → ℝ → ℂ := fun q u =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
        h k a b R K r q
  obtain ⟨B, _hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_even_le
      ha hb hR hstrong z hQ t H h k hr (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hM : Summable M := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left B
    simpa only [M, mul_assoc] using hbase
  have hFInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc (-H) H)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc (-H) H)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le horder]
    simpa only [F] using
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_arbitraryStrip
        (T := T) (c₀ := (1 / 2 : ℝ)) (c₁ := ((2 * Q : ℕ) : ℝ))
        (c := ((2 * Q : ℕ) : ℝ)) (by norm_num) (by norm_num)
        ⟨(by have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
             push_cast
             linarith), le_rfl⟩
        z t hH h k a b R K hr q
  have hmeas : AEStronglyMeasurable (fun u : ℝ => ∑' q : ℕ, F q u)
      (volume.restrict (Set.Icc (-H) H)) :=
    AEStronglyMeasurable.tsum (fun q => (hFInt q).aestronglyMeasurable)
  have hconst : Integrable (fun _u : ℝ => ∑' q : ℕ, M q)
      (volume.restrict (Set.Icc (-H) H)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le horder]
  change Integrable (fun u : ℝ => ∑' q : ℕ, F q u)
    (volume.restrict (Set.Icc (-H) H))
  apply hconst.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hnorm : Summable (fun q : ℕ => ‖F q u‖) :=
    hM.of_nonneg_of_le (fun q => norm_nonneg (F q u)) (fun q => by
      simpa only [F, M, A] using hbound q u hu)
  calc
    ‖∑' q : ℕ, F q u‖ ≤ ∑' q : ℕ, ‖F q u‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ℕ, M q :=
      hnorm.tsum_le_tsum (fun q => by
        simpa only [F, M, A] using hbound q u hu) hM


/-- Horizontal interval integrability of the physical positive series on an
arbitrary positive strip in the contour-exhaustion range. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (t H : ℝ) (hH : 1 ≤ |H|) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r)
      volume c₀ c₁ := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_arbitraryStrip
      hc₀ hc hc₀one (hughesYoungHeightWeight T t : ℂ) t H hH h k
        ha hb hr R K (T := T)

/-- Vertical interval integrability of the physical positive series on the
even opening line. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r)
      volume (-H) H := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_even
      ha hb hR hstrong (hughesYoungHeightWeight T t : ℂ) hQ t hH h k hr
        (T := T)

/-- Horizontal interval integrability of the coordinate-swapped negative
series on an arbitrary positive strip. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_horizontal_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (t H : ℝ) (hH : 1 ≤ |H|) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r)
      volume c₀ c₁ := by
  simpa only [
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive] using
    intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_arbitraryStrip
      hc₀ hc hc₀one (hughesYoungHeightWeight T t : ℂ) (-t) H hH k h
        hb ha hr R K (T := T)

/-- Vertical interval integrability of the coordinate-swapped negative
series on the even opening line. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_vertical_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r)
      volume (-H) H := by
  have hstrongSwap :
      hughesYoungDyadicRatio * ((b * a * R : ℕ) : ℝ) ≤
        hughesYoungDyadicRatio ^ (K + 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hstrong
  simpa only [
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive] using
    intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_even
      hb ha hR hstrongSwap (hughesYoungHeightWeight T t : ℂ) hQ (-t)
        hH k h hr (T := T)

/-- Every nonzero signed DFI shift of the height-weighted source has zero
contour integral between the low line and the even opening line. -/
theorem heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_boundaryRect_zero_even
    {T c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) {H : ℝ} (hH : 1 ≤ H)
    (h k : ℕ) {r : ℤ} (hr₀ : r ≠ 0) :
    (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralComplex
            T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
            h k a b R K r) -
      (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralComplex
            T t ((s : ℂ) + (H : ℂ) * I)
            h k a b R K r) +
      I • (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r) -
      I • (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralComplex
            T t ((c₀ : ℂ) + (u : ℂ) * I)
            h k a b R K r) = 0 := by
  cases r with
  | ofNat n =>
      by_cases hn0 : n = 0
      · subst n
        exact False.elim (hr₀ rfl)
      · have hn : 0 < n := Nat.pos_of_ne_zero hn0
        have hre (w : ℂ) :
            (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t w h k a b R K (n : ℤ) =
              hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                T t w h k a b R K n :=
          heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
            T t w h k a b R K n
        have hbottom :
            (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
                  h k a b R K (Int.ofNat n)) =
              ∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
                hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                  T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
                  h k a b R K n := by
          apply intervalIntegral.integral_congr
          intro s _hs
          exact hre _
        have htop :
            (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t ((s : ℂ) + (H : ℂ) * I)
                  h k a b R K (Int.ofNat n)) =
              ∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
                hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                  T t ((s : ℂ) + (H : ℂ) * I)
                  h k a b R K n := by
          apply intervalIntegral.integral_congr
          intro s _hs
          exact hre _
        have hright :
            (∫ u : ℝ in -H..H,
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
                  h k a b R K (Int.ofNat n)) =
              ∫ u : ℝ in -H..H,
                hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                  T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
                  h k a b R K n := by
          apply intervalIntegral.integral_congr
          intro u _hu
          exact hre _
        have hleft :
            (∫ u : ℝ in -H..H,
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t ((c₀ : ℂ) + (u : ℂ) * I)
                  h k a b R K (Int.ofNat n)) =
              ∫ u : ℝ in -H..H,
                hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                  T t ((c₀ : ℂ) + (u : ℂ) * I)
                  h k a b R K n := by
          apply intervalIntegral.integral_congr
          intro u _hu
          exact hre _
        rw [hbottom, htop, hright, hleft]
        exact
          hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero_even
            hc₀ hc₀one ha hb hR hstrong hQ t hH h k hn (T := T)
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by
        dsimp only [n]
        omega
      rw [hrCast]
      have hre (w : ℂ) :
          (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementSignedCentralComplex
                T t w h k a b R K (-(n : ℤ)) =
            hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
              T t w h k a b R K n :=
        heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
          T t w h k a b R K hn
      simp_rw [hre]
      exact
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_boundaryRect_zero_even
          hc₀ hc₀one ha hb hR hstrong hQ t hH h k hn (T := T)


/-- Every nonzero height-weighted signed source term is integrable on a
horizontal edge. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₀one : c₀ ≤ 1) (t H : ℝ) (hH : 1 ≤ |H|) (h k : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (R K : ℕ)
    {r : ℤ} (hr₀ : r ≠ 0) :
    IntervalIntegrable
      (fun s : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r)
      volume c₀ c₁ := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have hbase :=
        intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_arbitraryStrip
          hc₀ hc hc₀one t H hH h k ha hb hn R K (T := T)
      apply hbase.congr
      intro s _hs
      exact
        (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K n).symm
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by
        dsimp only [n]
        omega
      have hbase :=
        intervalIntegrable_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_horizontal_arbitraryStrip
          hc₀ hc hc₀one t H hH h k ha hb hn R K (T := T)
      apply hbase.congr
      intro s _hs
      rw [hrCast]
      exact
        (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K hn).symm


/-- Every nonzero height-weighted signed source term is integrable on a
vertical edge. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_vertical_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ) {r : ℤ} (hr₀ : r ≠ 0) :
    IntervalIntegrable
      (fun u : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r)
      volume (-H) H := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have hbase :=
        intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_even
          ha hb hR hstrong hQ t hH h k hn (T := T)
      apply hbase.congr
      intro u _hu
      exact
        (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K n).symm
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by
        dsimp only [n]
        omega
      have hbase :=
        intervalIntegrable_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_vertical_even
          ha hb hR hstrong hQ t hH h k hn (T := T)
      apply hbase.congr
      intro u _hu
      rw [hrCast]
      exact
        (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K hn).symm


/-- The complete finite signed Hughes--Young active-complement source has
zero contour integral between the low source line and the even opening line. -/
theorem heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_boundaryRect_zero_even
    {T c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) {H : ℝ} (hH : 1 ≤ H)
    (h k : ℕ) :
    (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
            h k a b R K) -
      (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((s : ℂ) + (H : ℂ) * I)
            h k a b R K) +
      I • (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K) -
      I • (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((c₀ : ℂ) + (u : ℂ) * I)
            h k a b R K) = 0 := by
  classical
  have hc : c₀ ≤ ((2 * Q : ℕ) : ℝ) := by
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    push_cast
    linarith
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hHabs : 1 ≤ |H| := by
    simpa [abs_of_nonneg hH₀] using hH
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let f : ℂ → ℤ → ℂ := fun w r =>
    (hughesYoungHeightWeight T t : ℂ) *
      (if r = 0 then 0 else
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t w h k a b R K r)
  have hBottom :
      (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)), ∑ r ∈ S,
          f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) =
        ∑ r ∈ S, ∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
          f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _hrmem
    by_cases hr₀ : r = 0
    · simp [f, hr₀]
    · simpa only [f, hr₀, if_false] using
        intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_arbitraryStrip
          hc₀ hc hc₀one t (-H) (by simpa using hHabs)
            h k ha hb R K hr₀ (T := T)
  have hTop :
      (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)), ∑ r ∈ S,
          f ((s : ℂ) + (H : ℂ) * I) r) =
        ∑ r ∈ S, ∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
          f ((s : ℂ) + (H : ℂ) * I) r := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _hrmem
    by_cases hr₀ : r = 0
    · simp [f, hr₀]
    · simpa only [f, hr₀, if_false] using
        intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_arbitraryStrip
          hc₀ hc hc₀one t H hHabs h k ha hb R K hr₀ (T := T)
  have hRight :
      (∫ u : ℝ in -H..H, ∑ r ∈ S,
          f (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) r) =
        ∑ r ∈ S, ∫ u : ℝ in -H..H,
          f (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) r := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _hrmem
    by_cases hr₀ : r = 0
    · simp [f, hr₀]
    · simpa only [f, hr₀, if_false] using
        intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_vertical_even
          ha hb hR hstrong hQ t hH₀ h k hr₀ (T := T)
  have hLeft :
      (∫ u : ℝ in -H..H, ∑ r ∈ S,
          f ((c₀ : ℂ) + (u : ℂ) * I) r) =
        ∑ r ∈ S, ∫ u : ℝ in -H..H,
          f ((c₀ : ℂ) + (u : ℂ) * I) r := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _hrmem
    by_cases hr₀ : r = 0
    · simp [f, hr₀]
    · simpa only [f, hr₀, if_false] using
        intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_vertical
          hc₀ hc₀one t hH₀ h k ha hb R K hr₀ (T := T)
  unfold hughesYoungNonLowerActiveComplementSignedSourceComplex
  simp_rw [Finset.mul_sum]
  change
    (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)), ∑ r ∈ S,
      f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) -
    (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)), ∑ r ∈ S,
      f ((s : ℂ) + (H : ℂ) * I) r) +
    I • (∫ u : ℝ in -H..H, ∑ r ∈ S,
      f (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) r) -
    I • (∫ u : ℝ in -H..H, ∑ r ∈ S,
      f ((c₀ : ℂ) + (u : ℂ) * I) r) = 0
  rw [hBottom, hTop, hRight, hLeft]
  simp only [smul_eq_mul]
  calc
    _ = ∑ r ∈ S,
        ((∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
            f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) -
          (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
            f ((s : ℂ) + (H : ℂ) * I) r) +
          I * (∫ u : ℝ in -H..H,
            f (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) r) -
          I * (∫ u : ℝ in -H..H,
            f ((c₀ : ℂ) + (u : ℂ) * I) r)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro r _hrmem
      by_cases hr₀ : r = 0
      · simp [f, hr₀]
      · simpa only [f, hr₀, if_false, smul_eq_mul] using
          heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_boundaryRect_zero_even
            hc₀ hc₀one ha hb hR hstrong hQ t hH h k hr₀ (T := T)


/-- The complete positive Ramanujan series inherits the same height-uniform
Gaussian envelope.  This is the Weierstrass summation step needed before the
horizontal contour edges can be sent to infinity. -/
theorem exists_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ |H| → ∀ c : ℝ,
      c ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r‖ ≤
      C * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
        (2 + |t| + c₁ + |H|) ^ 16) := by
  obtain ⟨B, hB, hterm⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le_arbitraryStripGaussian
      hc₀ hc hc₀one z t h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let Q : ℕ → ℝ := fun q => ((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hQ : Summable Q := by
    simpa only [Q] using summable_natCast_inv_sq_mul_four_log_profile_sq A hA
  let C₀ : ℝ := B * ∑' q : ℕ, Q q
  let C : ℝ := max 1 C₀
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro H hH c hcMem
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  let F : ℕ → ℂ := fun q =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r q
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hmajor : Summable (fun q : ℕ => (B * E) * Q q) :=
    hQ.mul_left (B * E)
  have hFbound (q : ℕ) : ‖F q‖ ≤ (B * E) * Q q := by
    simpa only [F, E, Q, A, mul_assoc] using hterm H hH q c hcMem
  have hF : Summable F := Summable.of_norm_bounded hmajor hFbound
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
  change ‖∑' q : ℕ, F q‖ ≤ _
  calc
    ‖∑' q : ℕ, F q‖ ≤ ∑' q : ℕ, ‖F q‖ :=
      norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' q : ℕ, (B * E) * Q q :=
      hF.norm.tsum_le_tsum hFbound hmajor
    _ = (B * E) * ∑' q : ℕ, Q q := by rw [tsum_mul_left]
    _ = C₀ * E := by dsimp only [C₀]; ring
    _ ≤ C * E := mul_le_mul_of_nonneg_right (le_max_right 1 C₀) hE0
    _ = C * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
        (2 + |t| + c₁ + |H|) ^ 16) := rfl


/-- The horizontal integral of the complete positive series has the same
Gaussian envelope, with only the length of the fixed source strip lost. -/
theorem exists_norm_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ |H| →
      ‖∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r‖ ≤
      (c₁ - c₀) * C *
        (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + |H|) ^ 16) := by
  obtain ⟨C, hC, hseries⟩ :=
    exists_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian_arbitraryStrip
      hc₀ hc hc₀one z t h k ha hb hr R K (T := T)
  refine ⟨C, hC, ?_⟩
  intro H hH
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  let f : ℝ → ℂ := fun s =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
      z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r
  have hpoint : ∀ s ∈ Set.uIoc c₀ c₁, ‖f s‖ ≤ C * E := by
    intro s hs
    have hs' : s ∈ Set.uIcc c₀ c₁ := Set.uIoc_subset_uIcc hs
    rw [Set.uIcc_of_le hc] at hs'
    exact hseries H hH s hs'
  have hInt : ‖∫ s : ℝ in c₀..c₁, f s‖ ≤ (C * E) * |c₁ - c₀| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := f) (C := C * E) hpoint
  have hlen : |c₁ - c₀| = c₁ - c₀ := abs_of_nonneg (sub_nonneg.mpr hc)
  change ‖∫ s : ℝ in c₀..c₁, f s‖ ≤ (c₁ - c₀) * C * E
  calc
    _ ≤ (C * E) * |c₁ - c₀| := hInt
    _ = (c₁ - c₀) * C * E := by rw [hlen]; ac_rfl


set_option maxHeartbeats 1200000 in
/-- The complete scalar-parametric positive equation-(27) series has a
vanishing upper horizontal edge. -/
theorem tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian_arbitraryStrip
      hc₀ hc hc₀one z t h k ha hb hr R K (T := T)
  let C₀ : ℝ := (c₁ - c₀) * C
  let B₀ : ℝ := 2 + |t| + c₁
  let envelope : ℝ → ℝ := fun H =>
    (c₁ - c₀) * C *
      (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) * (B₀ + H) ^ 16)
  have hC₀ : 0 ≤ C₀ := mul_nonneg (sub_nonneg.mpr hc) hC.le
  have hB₀ : 0 ≤ B₀ := by
    dsimp only [B₀]
    have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
    positivity
  have henv : Tendsto envelope atTop (𝓝 0) := by
    simpa only [envelope, C₀, mul_assoc] using
      tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen
        C₀ (100 * c₁ ^ 2) B₀ hC₀ hB₀
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ henv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    have hH0 : 0 ≤ H := zero_le_one.trans hH
    have hHabs : 1 ≤ |H| := by simpa only [abs_of_nonneg hH0] using hH
    have hb := hbound H hHabs
    simpa only [envelope, B₀, abs_of_nonneg hH0] using hb

set_option maxHeartbeats 1200000 in
/-- The complete scalar-parametric positive equation-(27) series also has a
vanishing lower horizontal edge. -/
theorem tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian_arbitraryStrip
      hc₀ hc hc₀one z t h k ha hb hr R K (T := T)
  let C₀ : ℝ := (c₁ - c₀) * C
  let B₀ : ℝ := 2 + |t| + c₁
  let envelope : ℝ → ℝ := fun H =>
    (c₁ - c₀) * C *
      (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) * (B₀ + H) ^ 16)
  have hC₀ : 0 ≤ C₀ := mul_nonneg (sub_nonneg.mpr hc) hC.le
  have hB₀ : 0 ≤ B₀ := by
    dsimp only [B₀]
    have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
    positivity
  have henv : Tendsto envelope atTop (𝓝 0) := by
    simpa only [envelope, C₀, mul_assoc] using
      tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen
        C₀ (100 * c₁ ^ 2) B₀ hC₀ hB₀
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ henv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    have hH0 : 0 ≤ H := zero_le_one.trans hH
    have hHabs : 1 ≤ |-H| := by simpa only [abs_neg, abs_of_nonneg hH0] using hH
    have hb := hbound (-H) hHabs
    rw [abs_neg, abs_of_nonneg hH0, neg_sq] at hb
    simpa only [envelope, B₀] using hb


/-- Vanishing upper horizontal edge for the physical positive series on an
arbitrary positive strip. -/
theorem tendsto_integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop_arbitraryStrip
      hc₀ hc hc₀one (hughesYoungHeightWeight T t : ℂ) t h k
        ha hb hr R K (T := T)

/-- Vanishing lower horizontal edge for the physical positive series on an
arbitrary positive strip. -/
theorem tendsto_integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop_arbitraryStrip
      hc₀ hc hc₀one (hughesYoungHeightWeight T t : ℂ) t h k
        ha hb hr R K (T := T)

/-- Vanishing upper horizontal edge for the coordinate-swapped negative
series on an arbitrary positive strip. -/
theorem tendsto_integral_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_horizontal_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  simp_rw [hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive]
  exact
    tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop_arbitraryStrip
      hc₀ hc hc₀one (hughesYoungHeightWeight T t : ℂ) (-t) k h
        hb ha hr R K (T := T)

/-- Vanishing lower horizontal edge for the coordinate-swapped negative
series on an arbitrary positive strip. -/
theorem tendsto_integral_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_bottom_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
        T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  simp_rw [hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive]
  exact
    tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop_arbitraryStrip
      hc₀ hc hc₀one (hughesYoungHeightWeight T t : ℂ) (-t) k h
        hb ha hr R K (T := T)

/-- Each nonzero signed DFI shift has a vanishing upper horizontal edge. -/
theorem tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) {r : ℤ} (hr₀ : r ≠ 0) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have hbase :=
        tendsto_integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop_arbitraryStrip
          hc₀ hc hc₀one t h k ha hb hn R K (T := T)
      convert hbase using 1
      ext H
      apply intervalIntegral.integral_congr
      intro s _hs
      exact heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K n
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
      have hbase :=
        tendsto_integral_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_horizontal_atTop_arbitraryStrip
          hc₀ hc hc₀one t h k ha hb hn R K (T := T)
      convert hbase using 1
      ext H
      apply intervalIntegral.integral_congr
      intro s _hs
      rw [hrCast]
      exact heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K hn

/-- Each nonzero signed DFI shift has a vanishing lower horizontal edge. -/
theorem tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_bottom_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) {r : ℤ} (hr₀ : r ≠ 0) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have hbase :=
        tendsto_integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop_arbitraryStrip
          hc₀ hc hc₀one t h k ha hb hn R K (T := T)
      convert hbase using 1
      ext H
      apply intervalIntegral.integral_congr
      intro s _hs
      exact heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
        T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K n
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
      have hbase :=
        tendsto_integral_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_bottom_atTop_arbitraryStrip
          hc₀ hc hc₀one t h k ha hb hn R K (T := T)
      convert hbase using 1
      ext H
      apply intervalIntegral.integral_congr
      intro s _hs
      rw [hrCast]
      exact heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
        T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K hn


/-- The complete finite signed DFI source has a vanishing upper horizontal
edge on the full strip from the source line to an arbitrary opening line. -/
theorem tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_horizontal_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K) atTop (𝓝 0) := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let f : ℂ → ℤ → ℂ := fun w r =>
    (hughesYoungHeightWeight T t : ℂ) *
      (if r = 0 then 0 else
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t w h k a b R K r)
  have hterm : ∀ r ∈ S, Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      f ((s : ℂ) + (H : ℂ) * I) r) atTop (𝓝 0) := by
    intro r _hrmem
    by_cases hr₀ : r = 0
    · subst r
      simpa only [f, if_pos, mul_zero, intervalIntegral.integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _H : ℝ => (0 : ℂ)) atTop (nhds 0))
    · simpa only [f, hr₀, if_false] using
        tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_atTop_arbitraryStrip
          hc₀ hc hc₀one t h k ha hb R K hr₀ (T := T)
  have hsum : Tendsto (fun H : ℝ => ∑ r ∈ S,
      ∫ s : ℝ in c₀..c₁, f ((s : ℂ) + (H : ℂ) * I) r) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum S hterm
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHabs : 1 ≤ |H| := by simpa only [abs_of_nonneg hH0] using hH
  have hpoint (w : ℂ) :
      (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t w h k a b R K =
        ∑ r ∈ S, f w r := by
    simp only [hughesYoungNonLowerActiveComplementSignedSourceComplex]
    dsimp only [B, S, f]
    rw [Finset.mul_sum]
  calc
    (∑ r ∈ S, ∫ s : ℝ in c₀..c₁,
        f ((s : ℂ) + (H : ℂ) * I) r) =
      ∫ s : ℝ in c₀..c₁, ∑ r ∈ S,
        f ((s : ℂ) + (H : ℂ) * I) r := by
      symm
      rw [intervalIntegral.integral_finsetSum]
      intro r _hrmem
      by_cases hr₀ : r = 0
      · simp [f, hr₀]
      · simpa only [f, hr₀, if_false] using
          intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_arbitraryStrip
            hc₀ hc hc₀one t H hHabs h k ha hb R K hr₀ (T := T)
    _ = ∫ s : ℝ in c₀..c₁,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((s : ℂ) + (H : ℂ) * I) h k a b R K := by
      apply intervalIntegral.integral_congr
      intro s _hs
      exact (hpoint _).symm

/-- The complete finite signed DFI source has a vanishing lower horizontal
edge on the full strip from the source line to an arbitrary opening line. -/
theorem tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_bottom_atTop_arbitraryStrip
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₀one : c₀ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K) atTop (𝓝 0) := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let f : ℂ → ℤ → ℂ := fun w r =>
    (hughesYoungHeightWeight T t : ℂ) *
      (if r = 0 then 0 else
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t w h k a b R K r)
  have hterm : ∀ r ∈ S, Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) atTop (𝓝 0) := by
    intro r _hrmem
    by_cases hr₀ : r = 0
    · subst r
      simpa only [f, if_pos, mul_zero, intervalIntegral.integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _H : ℝ => (0 : ℂ)) atTop (nhds 0))
    · simpa only [f, hr₀, if_false] using
        tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_bottom_atTop_arbitraryStrip
          hc₀ hc hc₀one t h k ha hb R K hr₀ (T := T)
  have hsum : Tendsto (fun H : ℝ => ∑ r ∈ S,
      ∫ s : ℝ in c₀..c₁,
        f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum S hterm
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHabs : 1 ≤ |-H| := by
    simpa only [abs_neg, abs_of_nonneg hH0] using hH
  have hpoint (w : ℂ) :
      (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t w h k a b R K =
        ∑ r ∈ S, f w r := by
    simp only [hughesYoungNonLowerActiveComplementSignedSourceComplex]
    dsimp only [B, S, f]
    rw [Finset.mul_sum]
  calc
    (∑ r ∈ S, ∫ s : ℝ in c₀..c₁,
        f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) =
      ∫ s : ℝ in c₀..c₁, ∑ r ∈ S,
        f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r := by
      symm
      rw [intervalIntegral.integral_finsetSum]
      intro r _hrmem
      by_cases hr₀ : r = 0
      · simp [f, hr₀]
      · simpa only [f, hr₀, if_false] using
          intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_arbitraryStrip
            hc₀ hc hc₀one t (-H) hHabs h k ha hb R K hr₀ (T := T)
    _ = ∫ s : ℝ in c₀..c₁,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K := by
      apply intervalIntegral.integral_congr
      intro s _hs
      exact (hpoint _).symm

/-- The complete signed DFI source may be moved from its low Mellin line to
the genuine even opening line.  This removes the former artificial
restriction that both vertical lines have real part at most one. -/
theorem tendsto_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_sub_zero_even
    {T c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀one : c₀ ≤ 1)
    {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) (h k : ℕ) :
    Tendsto (fun H : ℝ =>
      (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k a b R K) -
      (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K))
      atTop (nhds 0) := by
  have hc : c₀ ≤ ((2 * Q : ℕ) : ℝ) := by
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    push_cast
    linarith
  let F : ℂ → ℂ := fun w =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementSignedSourceComplex
        T t w h k a b R K
  change Tendsto (fun H : ℝ =>
    (∫ u : ℝ in -H..H, F (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)) -
    (∫ u : ℝ in -H..H, F ((c₀ : ℂ) + (u : ℂ) * I)))
    atTop (nhds 0)
  have htop : Tendsto (fun H : ℝ =>
      ∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        F ((s : ℂ) + (H : ℂ) * I)) atTop (nhds 0) := by
    simpa only [F] using
      tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_horizontal_atTop_arbitraryStrip
        hc₀ hc hc₀one t h k ha hb R K (T := T)
  have hbottom : Tendsto (fun H : ℝ =>
      ∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
        F ((s : ℂ) + ((-H : ℝ) : ℂ) * I)) atTop (nhds 0) := by
    simpa only [F] using
      tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_bottom_atTop_arbitraryStrip
        hc₀ hc hc₀one t h k ha hb R K (T := T)
  have hhorizontal : Tendsto (fun H : ℝ =>
      (-I) *
        ((∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
            F ((s : ℂ) + (H : ℂ) * I)) -
          (∫ s : ℝ in c₀..(((2 * Q : ℕ) : ℝ)),
            F ((s : ℂ) + ((-H : ℝ) : ℂ) * I))))
      atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using (htop.sub hbottom).const_mul (-I)
  apply hhorizontal.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
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
  rw [← hI, ← mul_assoc]
  have hnegI : (-I : ℂ) * I = 1 := by
    rw [neg_mul, I_mul_I]
    simp
  rw [hnegI, one_mul]


/-- The complete scalar-parametric positive Ramanujan series retains the
arbitrary even-line conductor saving. -/
theorem norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_even_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ)
    {r : ℕ} (hr : 0 < r) :
    ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r‖ ≤
      hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
          z T t u Q h k a b R r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let C : ℝ :=
    hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
      z T t u Q h k a b R r
  let F : ℕ → ℂ := fun q =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
        h k a b R K r q
  let M : ℕ → ℝ := fun q =>
    C * (((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hM : Summable M := by
    simpa only [M, mul_assoc] using
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left C
  have hpoint (q : ℕ) : ‖F q‖ ≤ M q := by
    simpa only [F, M, C, A] using
      norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_even_le_prefactor
        ha hb hR hstrong z hQ t u h k hr q
  have hF : Summable F := Summable.of_norm_bounded hM hpoint
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
  change ‖∑' q : ℕ, F q‖ ≤ _
  calc
    ‖∑' q : ℕ, F q‖ ≤ ∑' q : ℕ, ‖F q‖ :=
      norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' q : ℕ, M q := hF.norm.tsum_le_tsum hpoint hM
    _ = C * (∑' q : ℕ,
        ((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2) := by
      rw [tsum_mul_left]
    _ = _ := rfl

/-- Coordinate-swapped negative shifts satisfy the same scalar opening-line
estimate, with the critical-line variables and the arithmetic coordinates
interchanged exactly as in the DFI signed decomposition. -/
theorem norm_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_even_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ)
    {r : ℕ} (hr : 0 < r) :
    ‖hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
        T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r‖ ≤
      hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
          (hughesYoungHeightWeight T t : ℂ) T (-t) u Q k h b a R r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget b a r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  rw [hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive]
  exact
    norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_even_le
      hb ha hR (by simpa only [Nat.mul_comm a b] using hstrong)
      (hughesYoungHeightWeight T t : ℂ) hQ (-t) u k h hr

/-- The exact positive/negative opening-line majorant for a nonzero signed
DFI shift.  The two branches deliberately retain their different coordinate
order, matching the source's signed central-series definition. -/
noncomputable def hughesYoungNonLowerActiveComplementEvenSignedMajorant
    (T t u : ℝ) (Q h k a b R : ℕ) : ℤ → ℝ
  | Int.ofNat r =>
      hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
          (hughesYoungHeightWeight T t : ℂ) T t u Q h k a b R r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2)
  | Int.negSucc m =>
      let r := m + 1
      hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
          (hughesYoungHeightWeight T t : ℂ) T (-t) u Q k h b a R r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget b a r +
            4 * Real.log (q : ℝ)) ^ 2)

theorem hughesYoungNonLowerActiveComplementEvenSignedMajorant_nonneg
    (T t u : ℝ) (Q h k a b R : ℕ) (r : ℤ) :
    0 ≤ hughesYoungNonLowerActiveComplementEvenSignedMajorant
      T t u Q h k a b R r := by
  cases r with
  | ofNat n =>
      simp only [hughesYoungNonLowerActiveComplementEvenSignedMajorant]
      exact mul_nonneg
        (hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_nonneg
          (hughesYoungHeightWeight T t : ℂ) T t u Q h k a b R n)
        (tsum_nonneg fun _ => mul_nonneg (by positivity) (sq_nonneg _))
  | negSucc m =>
      simp only [hughesYoungNonLowerActiveComplementEvenSignedMajorant]
      exact mul_nonneg
        (hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_nonneg
          (hughesYoungHeightWeight T t : ℂ) T (-t) u Q k h b a R (m + 1))
        (tsum_nonneg fun _ => mul_nonneg (by positivity) (sq_nonneg _))

/-- Every nonzero signed DFI shift is controlled on the even opening line
by the corresponding exact branch of the signed majorant. -/
theorem norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_even_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ)
    {r : ℤ} (hr₀ : r ≠ 0) :
    ‖(hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r‖ ≤
      hughesYoungNonLowerActiveComplementEvenSignedMajorant
        T t u Q h k a b R r := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have heq :=
        heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K n
      change
        ‖(hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementSignedCentralComplex
              T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
                h k a b R K (n : ℤ)‖ ≤
          hughesYoungNonLowerActiveComplementEvenSignedMajorant
            T t u Q h k a b R (n : ℤ)
      rw [heq]
      simpa only [hughesYoungNonLowerActiveComplementEvenSignedMajorant,
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
        norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_even_le
          ha hb hR hstrong (hughesYoungHeightWeight T t : ℂ) hQ t u h k hn
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
      have heq :=
        heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K hn
      rw [hrCast, heq]
      simpa only [hughesYoungNonLowerActiveComplementEvenSignedMajorant] using
        norm_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_even_le
          ha hb hR hstrong hQ t u h k hn

/-- The complete finite signed source on the opening line is bounded by the
finite sum of its exact positive/negative shift majorants. -/
theorem norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_even_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ) :
    ‖(hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K‖ ≤
      ∑ r ∈ hughesYoungShiftInterval a b
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        if r = 0 then 0 else
          hughesYoungNonLowerActiveComplementEvenSignedMajorant
            T t u Q h k a b R r := by
  classical
  unfold hughesYoungNonLowerActiveComplementSignedSourceComplex
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro r _hr
  by_cases hr₀ : r = 0
  · subst r
    simp
  · simp only [hr₀, if_false]
    exact
      norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_even_le
        ha hb hR hstrong hQ t u h k hr₀

/-- The part of the even-opening-line positive central bound which is
independent of the Ramanujan modulus. -/
noncomputable def hughesYoungNonLowerActiveComplementEvenPositivePrefactor
    (T t u : ℝ) (Q h k a b R r : ℕ) : ℝ :=
  ‖((a : ℂ) * b)⁻¹‖ * (((a * b * r ^ 2 : ℕ) : ℝ)) * (r : ℝ) *
    (‖hughesYoungHeightWeight T t‖ *
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖ *
      (((a * b * R : ℕ) : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2))) *
      ((r : ℝ) ^ (-2 : ℝ)) *
      (2312 * max 1
          (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
            (-(3 / 4 : ℝ))) + 72))

theorem hughesYoungNonLowerActiveComplementEvenPositivePrefactor_nonneg
    (T t u : ℝ) (Q h k a b R r : ℕ) :
    0 ≤ hughesYoungNonLowerActiveComplementEvenPositivePrefactor
      T t u Q h k a b R r := by
  unfold hughesYoungNonLowerActiveComplementEvenPositivePrefactor
  positivity

/-- Modulus-separated form of the even-opening-line estimate. -/
theorem norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_even_le_prefactor
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ)
    {r : ℕ} (hr : 0 < r) (q : ℕ) :
    ‖hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
        T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r q‖ ≤
      hughesYoungNonLowerActiveComplementEvenPositivePrefactor
          T t u Q h k a b R r *
        (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  refine (norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_even_le
    ha hb hR hstrong hQ t u h k hr).trans_eq ?_
  unfold hughesYoungNonLowerActiveComplementEvenPositivePrefactor
  ring

set_option maxHeartbeats 1000000 in
/-- The complete positive-shift Ramanujan series retains the arbitrary
even-line conductor saving. -/
theorem norm_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_even_le
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) (h k : ℕ)
    {r : ℕ} (hr : 0 < r) :
    ‖hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
          h k a b R K r‖ ≤
      hughesYoungNonLowerActiveComplementEvenPositivePrefactor
          T t u Q h k a b R r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let C : ℝ := hughesYoungNonLowerActiveComplementEvenPositivePrefactor
    T t u Q h k a b R r
  let F : ℕ → ℂ := fun q =>
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
        h k a b R K r q
  let M : ℕ → ℝ := fun q =>
    C * (((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hM : Summable M := by
    simpa only [M, mul_assoc] using
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left C
  have hpoint (q : ℕ) : ‖F q‖ ≤ M q := by
    simpa only [F, M, C, A] using
      norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_even_le_prefactor
        ha hb hR hstrong hQ t u h k hr q
  have hF : Summable F :=
    Summable.of_norm_bounded hM hpoint
  unfold hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
  change ‖∑' q : ℕ, F q‖ ≤ _
  calc
    ‖∑' q : ℕ, F q‖ ≤ ∑' q : ℕ, ‖F q‖ :=
      norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' q : ℕ, M q :=
      hF.norm.tsum_le_tsum hpoint hM
    _ = C * (∑' q : ℕ,
        ((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2) := by
      rw [tsum_mul_left]
    _ = _ := rfl

/-! ## Whole-line opening integrability

The contour exhaustion above becomes an identity of genuine Bochner
integrals only after both vertical families have been shown integrable.  We
first record compact integrability of the complete finite signed source; this
also supplies its global strong measurability by exhaustion with unit
intervals. -/

/-- Compact vertical integrability of the complete finite signed source on an
arbitrary even opening line. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) {H : ℝ} (hH : 0 ≤ H) (h k : ℕ) :
    IntervalIntegrable
      (fun u : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K)
      volume (-H) H := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let f : ℤ → ℝ → ℂ := fun r u =>
    if r = 0 then 0 else
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K r
  have hsum : IntervalIntegrable
      (∑ r ∈ hughesYoungShiftInterval a b B B, f r)
      volume (-H) H :=
    IntervalIntegrable.sum (hughesYoungShiftInterval a b B B)
      fun r _hrmem => by
        by_cases hr₀ : r = 0
        · simp [f, hr₀]
        · simp only [f, hr₀, if_false]
          exact
            intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_vertical_even
              ha hb hR hstrong hQ t hH h k hr₀
  refine hsum.congr ?_
  intro u _hu
  unfold hughesYoungNonLowerActiveComplementSignedSourceComplex
  simp only [B, f, Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hrmem
  by_cases hr₀ : r = 0 <;> simp [hr₀]

/-- The complete opening-line source is strongly measurable on the whole
ordinate line.  The proof exhausts `ℝ` by the unit intervals appearing in
`iUnion_Icc_intCast`; no global continuity assertion is assumed. -/
theorem aestronglyMeasurable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even
    {T : ℝ} {a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t : ℝ) (h k : ℕ) :
    AEStronglyMeasurable
      (fun u : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k a b R K) := by
  let F : ℝ → ℂ := fun u => (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungNonLowerActiveComplementSignedSourceComplex
      T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
        h k a b R K
  rw [show volume = volume.restrict (Set.univ : Set ℝ) by simp]
  rw [← iUnion_Icc_intCast ℝ, aestronglyMeasurable_iUnion_iff]
  intro n
  let H : ℝ := |(n : ℝ)| + 2
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hlocal : IntegrableOn F (Set.Icc (-H) H) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    simpa only [F] using
      intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_even
        ha hb hR hstrong hQ t hH h k
  have hsubset : Set.Icc (n : ℝ) (n + 1 : ℝ) ⊆ Set.Icc (-H) H := by
    intro u hu
    dsimp only [H]
    constructor
    · have hn := neg_abs_le (n : ℝ)
      exact le_trans (by linarith : -(|(n : ℝ)| + 2) ≤ (n : ℝ)) hu.1
    · have hn := le_abs_self (n : ℝ)
      exact hu.2.trans (by linarith : (n : ℝ) + 1 ≤ |(n : ℝ)| + 2)
  exact (hlocal.mono_set hsubset).aestronglyMeasurable

/-- Gaussian-polynomial profile used to dominate the whole even opening
line. -/
noncomputable def hughesYoungNonLowerActiveComplementEvenGaussian
    (Q : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (4 * Q + 16)

theorem integrable_hughesYoungNonLowerActiveComplementEvenGaussian
    (Q : ℕ) :
    Integrable (hughesYoungNonLowerActiveComplementEvenGaussian Q) := by
  exact integrable_exp_neg_84_mul_one_add_abs_pow (4 * Q + 16)

/-- On the physical height support the reduced Mellin scalar is integrable
on every even opening line. -/
theorem integrable_norm_hughesYoungReducedMellinScaleConstantComplex_vertical_even
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) {Q : ℕ} (hQ : 0 < Q)
    (h k : ℕ) :
    Integrable (fun u : ℝ =>
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖) := by
  let C : ℝ :=
    ‖hughesYoungReducedMellinStaticComplex T t h k
      (((2 * Q : ℕ) : ℝ) : ℂ)‖ *
      (160000 * (2 * (Q : ℝ) + 1) ^ 8 *
        Real.exp (400 * (Q : ℝ) ^ 2) *
        ((7 + 2 * (Q : ℝ)) * T) ^ (4 * Q + 8))
  have hmeas : AEStronglyMeasurable (fun u : ℝ =>
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k‖) := by
    have hcont : Continuous (fun u : ℝ =>
        hughesYoungReducedMellinScaleConstantComplex T t
          (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I) h k) := by
      rw [continuous_iff_continuousAt]
      intro u
      have h2Q : (0 : ℝ) < ((2 * Q : ℕ) : ℝ) := by positivity
      exact
        (differentiableAt_hughesYoungReducedMellinScaleConstantComplex
          T t h k (by simpa using h2Q)).continuousAt.comp (by fun_prop)
    exact hcont.norm.aestronglyMeasurable
  apply ((integrable_hughesYoungNonLowerActiveComplementEvenGaussian Q).const_mul C).mono'
    hmeas
  filter_upwards with u
  have hright := norm_hughesYoungRightContourWeight_even_le_on_height_support
    hT ht hQ u
  rw [hughesYoungReducedMellinScaleConstantComplex_eq_static_mul_contour,
    norm_mul,
    norm_hughesYoungReducedMellinStaticComplex_horizontal,
    hughesYoungRightContourWeightComplex_vertical]
  calc
    _ ≤ ‖hughesYoungReducedMellinStaticComplex T t h k
          (((2 * Q : ℕ) : ℝ) : ℂ)‖ *
        (160000 * (2 * (Q : ℝ) + 1) ^ 8 *
          Real.exp (400 * (Q : ℝ) ^ 2 - 84 * u ^ 2) *
          ((7 + 2 * (Q : ℝ)) * T * (1 + |u|)) ^ (4 * Q + 8) *
          (1 + |u|) ^ 8) := by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hright)
        (norm_nonneg (hughesYoungReducedMellinStaticComplex T t h k
          (((2 * Q : ℕ) : ℝ) : ℂ)))
    _ = C * hughesYoungNonLowerActiveComplementEvenGaussian Q u := by
      rw [show Real.exp (400 * (Q : ℝ) ^ 2 - 84 * u ^ 2) =
          Real.exp (400 * (Q : ℝ) ^ 2) * Real.exp (-84 * u ^ 2) by
        rw [← Real.exp_add]
        congr 1
        ring,
        mul_pow]
      unfold C hughesYoungNonLowerActiveComplementEvenGaussian
      ring


end RiemannZeta.GuthMaynard

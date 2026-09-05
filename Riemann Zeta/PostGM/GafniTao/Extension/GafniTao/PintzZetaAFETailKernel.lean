import GafniTao.PintzZetaAFENormalizationTail

/-!
# Uniform far-tail kernels for the displaced zeta AFE

These estimates retain every source of height dependence.  In particular,
the inverse completed-zeta normalization is not absorbed into a constant.
The Gaussian will absorb this explicit envelope only in the subsequent
integral theorem.
-/

open Complex

namespace GafniTao

noncomputable section

/-- A uniform global majorant for one coefficient on the original displaced
edge.  It is intentionally rough away from the central range. -/
theorem exists_norm_pintzZetaAFETerm_original_global_le
    {r q : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hq : 0 < q) (hqr : q < r) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (t u : ℝ) (n : ℕ),
      1 ≤ |t| → n ≠ 0 →
      ‖pintzZetaAFETermContourIntegrand
          (((r : ℝ) : ℂ) + (t : ℂ) * I)
          (((r : ℝ) : ℂ) + (t : ℂ) * I) n
          (((-q : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
          (2 + |t| + |u|) ^ 2 *
          (Real.pi ^ (r / 2) *
            Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
            (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)) := by
  obtain ⟨D, hD, hnormalization⟩ :=
    exists_norm_pintzZetaAFENormalization_inv_le hrLower hrUpper
  obtain ⟨G, hG, hgamma⟩ :=
    exists_uniform_norm_GammaR_positive_strip
      (r₀ := r - q) (r₁ := r - q) (sub_pos.mpr hqr)
  let C : ℝ := G * q⁻¹
  have hC : 0 < C := mul_pos hG (inv_pos.mpr hq)
  refine ⟨C, D, hC, hD, ?_⟩
  intro t u n ht hn
  let s : ℂ := (r : ℂ) + (t : ℂ) * I
  let w : ℂ := ((-q : ℝ) : ℂ) + (u : ℂ) * I
  let z : ℂ := s + w
  let B : ℝ := 2 + |t| + |u|
  let Nrm : ℝ := Real.pi ^ (r / 2) *
    Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
    (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)
  have hB : 1 ≤ B := by
    dsimp only [B]
    linarith [abs_nonneg t, abs_nonneg u]
  have hzEq : z = ((r - q : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [z, s, w]
      ring_nf
    · simp [z, s, w]
  have hzNormCore : ‖z‖ ≤ 1 + (|t| + |u|) := by
    calc
      ‖z‖ ≤ |r - q| + |t + u| := by
        rw [hzEq]
        exact (norm_add_le ((r - q : ℝ) : ℂ)
          (((t + u : ℝ) : ℂ) * I)).trans_eq (by
            simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one])
      _ ≤ 1 + (|t| + |u|) := by
        have hrq : |r - q| ≤ 1 := by
          rw [abs_of_pos (sub_pos.mpr hqr)]
          linarith
        linarith [abs_add_le t u]
  have hzNorm : ‖z‖ ≤ B := hzNormCore.trans (by
    dsimp only [B]
    linarith)
  have honeSubNorm : ‖1 - z‖ ≤ B := by
    dsimp only [B]
    exact (norm_sub_le 1 z).trans (by
      norm_num
      linarith [hzNormCore])
  have hpoly : ‖z * (1 - z)‖ ≤ B ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hzNorm honeSubNorm (norm_nonneg _) (by positivity)
  have hgammaBound : ‖Complex.Gammaℝ z‖ ≤ G := by
    rw [hzEq]
    exact hgamma (r - q) (t + u) ⟨le_rfl, le_rfl⟩
  have hnormalizationBound :
      ‖(pintzZetaAFENormalization s)⁻¹‖ ≤ Nrm := by
    dsimp only [s, Nrm]
    exact hnormalization t ht
  have hzRe : z.re = r - q := by rw [hzEq]; simp
  have hdirichlet : ‖pintzZetaDirichletTerm z n‖ ≤ 1 :=
    norm_pintzZetaDirichletTerm_le_one hn (by rw [hzRe]; linarith)
  have hwInv : ‖w⁻¹‖ ≤ q⁻¹ := by
    simpa only [w, norm_inv] using norm_inv_neg_real_add_im_le (u := u) hq
  have hgauss : ‖Complex.exp (100 * w ^ 2)‖ =
      Real.exp (100 * q ^ 2 - 100 * u ^ 2) := by
    simpa only [w, neg_sq] using norm_pintzZetaAFE_gaussian_vertical (-q) u
  have hnonnegNrm : 0 ≤ Nrm := by dsimp only [Nrm]; positivity
  rw [norm_mul] at hpoly
  rw [norm_inv] at hnormalizationBound hwInv
  unfold pintzZetaAFETermContourIntegrand pintzZetaAFETermNumerator
  dsimp only
  simp only [norm_mul, div_eq_mul_inv, norm_inv]
  rw [show s + w = z by rfl, hgauss]
  calc
    Real.exp (100 * q ^ 2 - 100 * u ^ 2) * (‖z‖ * ‖1 - z‖) *
          ‖Complex.Gammaℝ z‖ * ‖pintzZetaAFENormalization s‖⁻¹ *
          ‖pintzZetaDirichletTerm z n‖ * ‖w‖⁻¹ ≤
        Real.exp (100 * q ^ 2 - 100 * u ^ 2) * B ^ 2 * G * Nrm * 1 * q⁻¹ := by
      gcongr
    _ = C * Real.exp (100 * q ^ 2 - 100 * u ^ 2) * B ^ 2 * Nrm := by
      dsimp only [C]
      ring_nf
    _ = C * Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
          (2 + |t| + |u|) ^ 2 *
          (Real.pi ^ (r / 2) *
            Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
            (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)) := rfl

/-- Global rough majorant for one coefficient on the reflected edge.  The
normalization remains that of the original point `r+it`. -/
theorem exists_norm_pintzZetaAFETerm_dual_global_le
    {r q : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hq : 0 < q) (hqDual : q < 1 - r) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (t u : ℝ) (n : ℕ),
      1 ≤ |t| → n ≠ 0 →
      ‖pintzZetaAFETermContourIntegrand
          (((r : ℝ) : ℂ) + (t : ℂ) * I)
          (1 - (((r : ℝ) : ℂ) + (t : ℂ) * I)) n
          (((-q : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
          (2 + |t| + |u|) ^ 2 *
          (Real.pi ^ (r / 2) *
            Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
            (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)) := by
  obtain ⟨D, hD, hnormalization⟩ :=
    exists_norm_pintzZetaAFENormalization_inv_le hrLower hrUpper
  obtain ⟨G, hG, hgamma⟩ :=
    exists_uniform_norm_GammaR_positive_strip
      (r₀ := 1 - r - q) (r₁ := 1 - r - q) (by linarith)
  let C : ℝ := G * q⁻¹
  have hC : 0 < C := mul_pos hG (inv_pos.mpr hq)
  refine ⟨C, D, hC, hD, ?_⟩
  intro t u n ht hn
  let s : ℂ := (r : ℂ) + (t : ℂ) * I
  let base : ℂ := 1 - s
  let w : ℂ := ((-q : ℝ) : ℂ) + (u : ℂ) * I
  let z : ℂ := base + w
  let B : ℝ := 2 + |t| + |u|
  let Nrm : ℝ := Real.pi ^ (r / 2) *
    Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
    (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)
  have hzEq : z = ((1 - r - q : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [z, base, s, w]
      ring_nf
    · simp [z, base, s, w]
  have hzNormCore : ‖z‖ ≤ 1 + (|t| + |u|) := by
    calc
      ‖z‖ ≤ |1 - r - q| + |-t + u| := by
        rw [hzEq]
        exact (norm_add_le ((1 - r - q : ℝ) : ℂ)
          (((-t + u : ℝ) : ℂ) * I)).trans_eq (by
            simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one])
      _ ≤ 1 + (|t| + |u|) := by
        have hbase : |1 - r - q| ≤ 1 := by
          rw [abs_of_pos (by linarith : 0 < 1 - r - q)]
          linarith
        have hheight := abs_add_le (-t) u
        rw [abs_neg] at hheight
        linarith
  have hzNorm : ‖z‖ ≤ B := hzNormCore.trans (by
    dsimp only [B]
    linarith)
  have honeSubNorm : ‖1 - z‖ ≤ B := by
    dsimp only [B]
    exact (norm_sub_le 1 z).trans (by
      norm_num
      linarith [hzNormCore])
  have hpoly : ‖z * (1 - z)‖ ≤ B ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hzNorm honeSubNorm (norm_nonneg _) (by positivity)
  have hgammaBound : ‖Complex.Gammaℝ z‖ ≤ G := by
    rw [hzEq]
    exact hgamma (1 - r - q) (-t + u) ⟨le_rfl, le_rfl⟩
  have hnormalizationBound :
      ‖(pintzZetaAFENormalization s)⁻¹‖ ≤ Nrm := by
    dsimp only [s, Nrm]
    exact hnormalization t ht
  have hzRe : z.re = 1 - r - q := by rw [hzEq]; simp
  have hdirichlet : ‖pintzZetaDirichletTerm z n‖ ≤ 1 :=
    norm_pintzZetaDirichletTerm_le_one hn (by rw [hzRe]; linarith)
  have hwInv : ‖w⁻¹‖ ≤ q⁻¹ := by
    simpa only [w, norm_inv] using norm_inv_neg_real_add_im_le (u := u) hq
  have hgauss : ‖Complex.exp (100 * w ^ 2)‖ =
      Real.exp (100 * q ^ 2 - 100 * u ^ 2) := by
    simpa only [w, neg_sq] using norm_pintzZetaAFE_gaussian_vertical (-q) u
  rw [norm_mul] at hpoly
  rw [norm_inv] at hnormalizationBound hwInv
  unfold pintzZetaAFETermContourIntegrand pintzZetaAFETermNumerator
  dsimp only
  simp only [norm_mul, div_eq_mul_inv, norm_inv]
  rw [show base + w = z by rfl, hgauss]
  calc
    Real.exp (100 * q ^ 2 - 100 * u ^ 2) * (‖z‖ * ‖1 - z‖) *
          ‖Complex.Gammaℝ z‖ * ‖pintzZetaAFENormalization s‖⁻¹ *
          ‖pintzZetaDirichletTerm z n‖ * ‖w‖⁻¹ ≤
        Real.exp (100 * q ^ 2 - 100 * u ^ 2) * B ^ 2 * G * Nrm * 1 * q⁻¹ := by
      gcongr
    _ = C * Real.exp (100 * q ^ 2 - 100 * u ^ 2) * B ^ 2 * Nrm := by
      dsimp only [C]
      ring_nf
    _ = C * Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
          (2 + |t| + |u|) ^ 2 *
          (Real.pi ^ (r / 2) *
            Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
            (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)) := rfl

/-- The explicit rough envelope on the far range is dominated by a fixed
Gaussian in `u` and an exponentially small factor in the physical height.
The numerical constants are deliberately slack and fully proved. -/
theorem pintzZetaAFEFarEnvelope_le
    {r q D t u : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hD : 0 ≤ D) (ht : 4 ≤ t) (hu : t / 2 ≤ |u|) :
    Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
        (2 + |t| + |u|) ^ 2 *
        (Real.pi ^ (r / 2) *
          Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
          (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)) ≤
      (2 * Real.pi ^ (r / 2) * Real.exp (100 * q ^ 2 + D / 4)) *
        Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2) := by
  have ht0 : 0 ≤ t := by linarith
  rw [abs_of_nonneg ht0, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
  have huTwo : 2 ≤ |u| := by linarith
  have htLe : t ≤ 2 * |u| := by linarith
  have hB : 2 + t + |u| ≤ 4 * |u| := by linarith
  have hBSq : (2 + t + |u|) ^ 2 ≤ 16 * u ^ 2 := by
    have := mul_self_le_mul_self
      (by linarith [abs_nonneg u] : 0 ≤ 2 + t + |u|) hB
    nlinarith [sq_abs u]
  have hPolyExp : (2 + t + |u|) ^ 2 ≤ Real.exp (16 * u ^ 2) := by
    have hexp := Real.add_one_le_exp (16 * u ^ 2)
    nlinarith [hBSq]
  have hlog : Real.log (t / 2 + 2) ≤ t := by
    have hx : 0 < t / 2 + 2 := by linarith
    exact (Real.log_le_sub_one_of_pos hx).trans (by linarith)
  have hdRange : 0 ≤ (1 - r) / 2 ∧ (1 - r) / 2 ≤ 1 / 4 := by
    constructor <;> linarith
  have hLogExponent :
      (Real.log (t / 2 + 2) + D) * ((1 - r) / 2) ≤
        D / 4 + t ^ 2 / 16 := by
    have htSq : t ≤ t ^ 2 / 4 := by nlinarith
    have hsum : 0 ≤ Real.log (t / 2 + 2) + D := by
      have : 1 ≤ t / 2 + 2 := by linarith
      exact add_nonneg (Real.log_nonneg this) hD
    have hmul := mul_le_mul_of_nonneg_left hdRange.2 hsum
    nlinarith
  have hCoshExp : Real.cosh (Real.pi * (t / 2)) ≤ Real.exp (2 * t ^ 2) := by
    calc
      Real.cosh (Real.pi * (t / 2)) ≤
          Real.exp ((Real.pi * (t / 2)) ^ 2 / 2) :=
        Real.cosh_le_exp_half_sq _
      _ ≤ Real.exp (2 * t ^ 2) := Real.exp_le_exp.mpr (by
        have hpiSq : Real.pi ^ 2 ≤ 16 := by
          nlinarith [Real.pi_pos, Real.pi_lt_four]
        nlinarith [sq_nonneg t])
  have hCoshFactor :
      1 + Real.cosh (Real.pi * (t / 2)) / Real.pi ≤
        2 * Real.exp (2 * t ^ 2) := by
    have hpiOne : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hcosh0 : 0 ≤ Real.cosh (Real.pi * (t / 2)) := (Real.cosh_pos _).le
    have hdiv : Real.cosh (Real.pi * (t / 2)) / Real.pi ≤
        Real.cosh (Real.pi * (t / 2)) :=
      div_le_self hcosh0 hpiOne
    have honeExp : 1 ≤ Real.exp (2 * t ^ 2) := by
      rw [Real.one_le_exp_iff]
      positivity
    nlinarith
  have hNormalization :
      Real.exp ((Real.log (t / 2 + 2) + D) * ((1 - r) / 2)) *
          (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi) ≤
        2 * Real.exp (D / 4) * Real.exp (3 * t ^ 2) := by
    calc
      _ ≤ Real.exp (D / 4 + t ^ 2 / 16) *
          (2 * Real.exp (2 * t ^ 2)) :=
        mul_le_mul (Real.exp_le_exp.mpr hLogExponent) hCoshFactor
          (by positivity) (by positivity)
      _ ≤ 2 * Real.exp (D / 4) * Real.exp (3 * t ^ 2) := by
        calc
          Real.exp (D / 4 + t ^ 2 / 16) *
              (2 * Real.exp (2 * t ^ 2)) =
            2 * Real.exp (D / 4) *
              Real.exp (t ^ 2 / 16 + 2 * t ^ 2) := by
                repeat' rw [Real.exp_add]
                ring_nf
          _ ≤ 2 * Real.exp (D / 4) * Real.exp (3 * t ^ 2) := by
            apply mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))
            positivity
  have huSq : t ^ 2 ≤ 4 * u ^ 2 := by
    have := mul_self_le_mul_self ht0 htLe
    nlinarith [sq_abs u]
  have hExponent :
      (-100 * u ^ 2) + 16 * u ^ 2 + 3 * t ^ 2 ≤
        -10 * t ^ 2 + -25 * u ^ 2 := by
    nlinarith
  calc
    Real.exp (100 * q ^ 2 - 100 * u ^ 2) * (2 + t + |u|) ^ 2 *
        (Real.pi ^ (r / 2) *
          Real.exp ((Real.log (t / 2 + 2) + D) * ((1 - r) / 2)) *
          (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)) ≤
      Real.exp (100 * q ^ 2 - 100 * u ^ 2) * Real.exp (16 * u ^ 2) *
        (Real.pi ^ (r / 2) *
          (2 * Real.exp (D / 4) * Real.exp (3 * t ^ 2))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hPolyExp (Real.exp_pos _).le
      · calc
          Real.pi ^ (r / 2) *
              Real.exp ((Real.log (t / 2 + 2) + D) * ((1 - r) / 2)) *
              (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi) =
            Real.pi ^ (r / 2) *
              (Real.exp ((Real.log (t / 2 + 2) + D) * ((1 - r) / 2)) *
                (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)) := by ring_nf
          _ ≤ Real.pi ^ (r / 2) *
              (2 * Real.exp (D / 4) * Real.exp (3 * t ^ 2)) :=
            mul_le_mul_of_nonneg_left hNormalization
              (Real.rpow_nonneg Real.pi_pos.le _)
      · positivity
      · positivity
    _ = (2 * Real.pi ^ (r / 2) * Real.exp (100 * q ^ 2 + D / 4)) *
        Real.exp ((-100 * u ^ 2) + 16 * u ^ 2 + 3 * t ^ 2) := by
      rw [sub_eq_add_neg]
      repeat' rw [Real.exp_add]
      ring_nf
    _ ≤ (2 * Real.pi ^ (r / 2) * Real.exp (100 * q ^ 2 + D / 4)) *
        Real.exp (-10 * t ^ 2 + -25 * u ^ 2) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExponent)
      positivity
    _ = (2 * Real.pi ^ (r / 2) * Real.exp (100 * q ^ 2 + D / 4)) *
        Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2) := by
      calc
        (2 * Real.pi ^ (r / 2) * Real.exp (100 * q ^ 2 + D / 4)) *
            Real.exp (-10 * t ^ 2 + -25 * u ^ 2) =
          (2 * Real.pi ^ (r / 2) * Real.exp (100 * q ^ 2 + D / 4)) *
            (Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2)) := by
              rw [← Real.exp_add]
        _ = _ := by ring_nf

/-- Central Gaussian completion used on both displaced edges. -/
theorem pintzZetaAFECentralGaussian_le (u : ℝ) :
    Real.exp (-100 * u ^ 2) * Real.exp (Real.pi * |u| / 4) ≤
      Real.exp (1 / 200) * Real.exp (-50 * u ^ 2) := by
  have hpi : Real.pi * |u| / 4 ≤ |u| := by
    have hu0 := abs_nonneg u
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hsquare : |u| ≤ 50 * u ^ 2 + 1 / 200 := by
    nlinarith [sq_nonneg (|u| - 1 / 100), sq_abs u]
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- All-height pointwise majorant on the original displaced edge.  The first
term is the source-strength conductor saving; the second is the explicit far
tail. -/
theorem exists_norm_pintzZetaAFETerm_original_all_height_le
    {r q : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hq : 0 < q) (hqr : q < r) :
    ∃ Ccentral Ctail : ℝ, 0 < Ccentral ∧ 0 < Ctail ∧
      ∀ (t u : ℝ) (n : ℕ), 4 ≤ t → n ≠ 0 →
      ‖pintzZetaAFETermContourIntegrand
          (((r : ℝ) : ℂ) + (t : ℂ) * I)
          (((r : ℝ) : ℂ) + (t : ℂ) * I) n
          (((-q : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        Ccentral * Real.exp (-50 * u ^ 2) *
            Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
            (n : ℝ) ^ (-(r - q)) +
          Ctail * Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2) := by
  obtain ⟨C₀, hC₀, hcentral⟩ :=
    exists_norm_pintzZetaAFETermContourIntegrand_left_central_le hq hqr hrUpper.le
  obtain ⟨C₁, D, hC₁, hD, hglobal⟩ :=
    exists_norm_pintzZetaAFETerm_original_global_le hrLower hrUpper hq hqr
  let Ccentral : ℝ := C₀ * Real.exp (1 / 200)
  let Ctail : ℝ := C₁ *
    (2 * Real.pi ^ (r / 2) * Real.exp (100 * q ^ 2 + D / 4))
  have hCcentral : 0 < Ccentral := mul_pos hC₀ (Real.exp_pos _)
  have hCtail : 0 < Ctail := by dsimp only [Ctail]; positivity
  refine ⟨Ccentral, Ctail, hCcentral, hCtail, ?_⟩
  intro t u n ht hn
  by_cases hu : |u| ≤ t / 2
  · have hraw := hcentral t u n ht hu hn
    have hgauss := pintzZetaAFECentralGaussian_le u
    calc
      _ ≤ C₀ * Real.exp (-100 * u ^ 2) * Real.exp (Real.pi * |u| / 4) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          (n : ℝ) ^ (-(r - q)) := hraw
      _ ≤ Ccentral * Real.exp (-50 * u ^ 2) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          (n : ℝ) ^ (-(r - q)) := by
        dsimp only [Ccentral]
        calc
          C₀ * Real.exp (-100 * u ^ 2) * Real.exp (Real.pi * |u| / 4) *
              Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
              (n : ℝ) ^ (-(r - q)) =
            (C₀ * (Real.exp (-100 * u ^ 2) *
              Real.exp (Real.pi * |u| / 4))) *
              (Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
                (n : ℝ) ^ (-(r - q))) := by ring_nf
          _ ≤ (C₀ * (Real.exp (1 / 200) * Real.exp (-50 * u ^ 2))) *
              (Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
                (n : ℝ) ^ (-(r - q))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgauss hC₀.le) (by positivity)
          _ = C₀ * Real.exp (1 / 200) * Real.exp (-50 * u ^ 2) *
              Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
              (n : ℝ) ^ (-(r - q)) := by ring_nf
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have huFar : t / 2 ≤ |u| := le_of_not_ge hu
    have hraw := hglobal t u n (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith) hn
    have henv := pintzZetaAFEFarEnvelope_le (q := q) (D := D)
      hrLower hrUpper hD.le ht huFar
    calc
      _ ≤ C₁ * (Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
          (2 + |t| + |u|) ^ 2 *
          (Real.pi ^ (r / 2) *
            Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
            (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi))) := by
        simpa only [mul_assoc] using hraw
      _ ≤ C₁ * ((2 * Real.pi ^ (r / 2) *
          Real.exp (100 * q ^ 2 + D / 4)) *
          Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2)) :=
        mul_le_mul_of_nonneg_left henv hC₁.le
      _ = Ctail * Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2) := by
        dsimp only [Ctail]
        ring_nf
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- All-height pointwise majorant on the reflected displaced edge. -/
theorem exists_norm_pintzZetaAFETerm_dual_all_height_le
    {r q : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hq : 0 < q) (hqDual : q < 1 - r) :
    ∃ Ccentral Ctail : ℝ, 0 < Ccentral ∧ 0 < Ctail ∧
      ∀ (t u : ℝ) (n : ℕ), 4 ≤ t → n ≠ 0 →
      ‖pintzZetaAFETermContourIntegrand
          (((r : ℝ) : ℂ) + (t : ℂ) * I)
          (1 - (((r : ℝ) : ℂ) + (t : ℂ) * I)) n
          (((-q : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        Ccentral * Real.exp (-50 * u ^ 2) *
            Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
            Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
            (n : ℝ) ^ (-(1 - r - q)) +
          Ctail * Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2) := by
  obtain ⟨C₀, hC₀, hcentral⟩ :=
    exists_norm_pintzZetaAFETermContourIntegrand_dual_central_le
      hrLower hrUpper hq hqDual
  obtain ⟨C₁, D, hC₁, hD, hglobal⟩ :=
    exists_norm_pintzZetaAFETerm_dual_global_le hrLower hrUpper hq hqDual
  let Ccentral : ℝ := C₀ * Real.exp (1 / 200)
  let Ctail : ℝ := C₁ *
    (2 * Real.pi ^ (r / 2) * Real.exp (100 * q ^ 2 + D / 4))
  have hCcentral : 0 < Ccentral := mul_pos hC₀ (Real.exp_pos _)
  have hCtail : 0 < Ctail := by dsimp only [Ctail]; positivity
  refine ⟨Ccentral, Ctail, hCcentral, hCtail, ?_⟩
  intro t u n ht hn
  by_cases hu : |u| ≤ t / 2
  · have hraw := hcentral t u n ht hu hn
    have hgauss := pintzZetaAFECentralGaussian_le u
    calc
      _ ≤ C₀ * Real.exp (-100 * u ^ 2) * Real.exp (Real.pi * |u| / 4) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
          (n : ℝ) ^ (-(1 - r - q)) := hraw
      _ ≤ Ccentral * Real.exp (-50 * u ^ 2) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
          (n : ℝ) ^ (-(1 - r - q)) := by
        dsimp only [Ccentral]
        calc
          C₀ * Real.exp (-100 * u ^ 2) * Real.exp (Real.pi * |u| / 4) *
              Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
              Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
              (n : ℝ) ^ (-(1 - r - q)) =
            (C₀ * (Real.exp (-100 * u ^ 2) *
              Real.exp (Real.pi * |u| / 4))) *
              (Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
                Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
                (n : ℝ) ^ (-(1 - r - q))) := by ring_nf
          _ ≤ (C₀ * (Real.exp (1 / 200) * Real.exp (-50 * u ^ 2))) *
              (Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
                Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
                (n : ℝ) ^ (-(1 - r - q))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgauss hC₀.le) (by positivity)
          _ = C₀ * Real.exp (1 / 200) * Real.exp (-50 * u ^ 2) *
              Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
              Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
              (n : ℝ) ^ (-(1 - r - q)) := by ring_nf
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have huFar : t / 2 ≤ |u| := le_of_not_ge hu
    have hraw := hglobal t u n (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith) hn
    have henv := pintzZetaAFEFarEnvelope_le (q := q) (D := D)
      hrLower hrUpper hD.le ht huFar
    calc
      _ ≤ C₁ * (Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
          (2 + |t| + |u|) ^ 2 *
          (Real.pi ^ (r / 2) *
            Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
            (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi))) := by
        simpa only [mul_assoc] using hraw
      _ ≤ C₁ * ((2 * Real.pi ^ (r / 2) *
          Real.exp (100 * q ^ 2 + D / 4)) *
          Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2)) :=
        mul_le_mul_of_nonneg_left henv hC₁.le
      _ = Ctail * Real.exp (-10 * t ^ 2) * Real.exp (-25 * u ^ 2) := by
        dsimp only [Ctail]
        ring_nf
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

#print axioms exists_norm_pintzZetaAFETerm_original_global_le
#print axioms exists_norm_pintzZetaAFETerm_dual_global_le
#print axioms pintzZetaAFEFarEnvelope_le
#print axioms pintzZetaAFECentralGaussian_le
#print axioms exists_norm_pintzZetaAFETerm_original_all_height_le
#print axioms exists_norm_pintzZetaAFETerm_dual_all_height_le

end

end GafniTao
